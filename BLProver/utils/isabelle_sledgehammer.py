"""
Isabelle .thy 后处理：
1) 对 sledgehammer 行提取 Try this 建议并回填
2) 对回填后的 theory 做验证
"""

from __future__ import annotations

import hashlib
import logging
import os
import re
import subprocess
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from .isabelle_server_lifecycle import (
    register_pool,
    register_server_pid,
    unregister_pool,
)

logger = logging.getLogger(__name__)


MAX_ISABELLE_WAIT_SEC = 60
"""Isabelle use_theories / sledgehammer 的 PIDE watchdog 等待上限（秒）。"""

MAX_VERIFY_WALL_TIMEOUT_SEC = 600
"""纯 verify 类调用的 wall-clock 硬超时上限（秒）。"""

STUCK_VERIFY_MARKER = "[STUCK_VERIFY]"
"""verify wall-clock 超时标记（对应 jEdit 紫色：证明命令仍在后台运行）。"""

SESSION_RESTART_DELAY_SEC = 5
"""session_stop 后等待再 session_start，避免 PIDE/PolyML 未完全释放。"""

SESSION_STOP_TIMEOUT_SEC = 30
"""session_stop RPC 最长等待（秒）；超时则强杀 server 避免 repair 循环永久阻塞。"""

WORKER_DRAIN_AFTER_FORCE_KILL_SEC = 60
"""wall-clock 超时强杀 server 后，等待后台 use_theories worker 退出的最长时间（秒）。"""


def _clamp_isabelle_wait(seconds: int) -> int:
    return min(max(1, int(seconds)), MAX_ISABELLE_WAIT_SEC)


def _clamp_verify_wall_timeout(seconds: int) -> int:
    return min(max(1, int(seconds)), MAX_VERIFY_WALL_TIMEOUT_SEC)


@dataclass
class IsabelleRunnerConfig:
    isabelle_path: str = "D:/software/Isabelle2025/Isabelle2025/contrib/cygwin/bin/bash.exe"
    isabelle_home: str = "D:/software/Isabelle2025/Isabelle2025"
    timeout: int = MAX_ISABELLE_WAIT_SEC
    """含 sledgehammer 的 use_theories 最长等待（秒）。"""
    verify_timeout: int = MAX_ISABELLE_WAIT_SEC
    """纯验证 / repair 后 verify 的 PIDE watchdog（秒，无进展触发）。"""
    verify_wall_timeout_sec: int = 300
    """verify 类调用的 wall-clock 硬超时（秒）；超时后按卡住处理并 sledgehammer 替换。"""
    use_theories_heartbeat_sec: int = 15
    """阻塞等待 Isabelle 时每 N 秒打印一次进度。"""
    max_sledgehammer_rounds: int = 3
    """sledgehammer 占位符回填最大轮次（论文 4.1.4：内层 3 次）。"""
    max_failure_repair_rounds: int = 3
    """验证失败后按报错行定向 sledgehammer 修复的最大轮次（论文 4.1.4：内层 3 次）。"""
    sledgehammer_backfill_mode: str = "sequential"
    """回填模式：sequential（一次一个洞）或 batch（整文件批量）。"""
    sledgehammer_hole_timeout_sec: int = 30
    """单个 sledgehammer 洞的 prover 时间上限（秒），用于估算整轮 wall-clock。"""
    sledgehammer_round_max_wall_sec: int = 900
    sledgehammer_wall_timeout_sec: int = 180
    """单次 sledgehammer 调用（含 theory 加载）的 wall-clock 上限（秒）；独立于 PIDE watchdog。"""
    """单轮 sledgehammer 回填的 wall-clock 上限（秒）。"""
    repair_budget_sec: int = 180
    """定向修复总预算（秒）；耗尽后立即交回外层 LLM 报错修复。"""
    fallback_candidate_timeout_sec: int = 45
    """无 Try this 时单个回退方法（by simp/blast/...）的验证超时（秒）。"""
    max_fallback_candidates: int = 6
    """无 Try this 时最多尝试的回退方法数量。"""
    sledgehammer_provers: str = "cvc5 vampire verit e z3 spass zipperposition"
    """定向修复时显式启用的 prover（逗号/空格分隔）；留空则用 Isabelle 默认值。"""
    sledgehammer_prover_timeout_sec: int = 30
    """单个 prover 的搜索时限（秒），写入 hammer 行的 timeout 选项。"""
    repair_failed_steps: bool = True
    use_server: bool = True
    kill_orphan_poly_on_shutdown: bool = True
    """Windows：正常 shutdown 后仍 taskkill 遗留的 poly.exe / bash_process.exe / eprover.exe。"""

    def __post_init__(self) -> None:
        self.timeout = _clamp_isabelle_wait(self.timeout)
        self.verify_timeout = _clamp_isabelle_wait(self.verify_timeout)
        self.verify_wall_timeout_sec = _clamp_verify_wall_timeout(
            self.verify_wall_timeout_sec
        )


def _stop_isabelle_session(
    client: Any,
    session_id: Optional[str],
    *,
    context: str,
    timeout_sec: Optional[int] = None,
) -> bool:
    """停止 PIDE session；成功/失败均打日志，便于对照 session 已就绪/已重启。"""
    if not client or not session_id:
        return True
    wait_sec = (
        SESSION_STOP_TIMEOUT_SEC if timeout_sec is None else max(1, int(timeout_sec))
    )
    err: List[Optional[BaseException]] = [None]
    done = threading.Event()

    def _worker() -> None:
        try:
            client.session_stop(session_id)
        except BaseException as exc:
            err[0] = exc
        finally:
            done.set()

    worker = threading.Thread(target=_worker, daemon=True)
    worker.start()
    if not done.wait(timeout=wait_sec):
        print(
            f"[isabelle_server] 警告: session_stop 超时 ({wait_sec}s, "
            f"{session_id}, {context})",
            flush=True,
        )
        return False
    if err[0] is not None:
        msg = (
            f"[isabelle_server] 警告: session_stop 失败 "
            f"({session_id}, {context}): {err[0]}"
        )
        print(msg, flush=True)
        logger.warning(msg)
        return False
    print(
        f"[isabelle_server] session 已停止: {session_id} ({context})",
        flush=True,
    )
    return True


# 仅对“证明步骤失败”类错误做定向 sledgehammer 修复（结构/语法错误替换无效）
_REPAIRABLE_ERROR_FRAGMENTS = (
    "Failed to finish proof",
    "Failed to apply initial proof method",
    "Failed to apply proof method",
    "Failed to refine",
    "At command",  # CLI: *** At command "by" (line N ...)
    "OF: no unifiers",  # 引理 OF 实例化失败（如 values_push_other[OF ...]）
    "exception THM",  # server 模式下 THM/OF 异常的包装
)

_SKIP_LINE_HEAD = re.compile(
    r"^\s*(theorem|lemma|proof|qed|typ|imports|begin|end|definition|fun|"
    r"subsubsection|locale|context|interpretation|sublocale)\b",
    re.IGNORECASE,
)

_PROOF_STEP_LINE = re.compile(
    r"^\s+("
    r"using\b.+\bby\s+"
    r"|using\b.+\s*\.\s*$"
    r"|unfolding\b.+\bby\s+"
    r"|unfolding\b.+\s*\.\s*$"
    r"|by\s+"
    r"|sledgehammer(?:\s*\[[^\]]*\])?\s*$"
    r")",
    re.IGNORECASE,
)

_SLEDGEHAMMER_LINE = re.compile(
    r"\bsledgehammer(?:\s*\[[^\]]*\])?\s*$",
    re.MULTILINE,
)

_ISABELLE_ERROR_MESSAGE_KINDS = frozenset({"error"})

_ISABELLE_SERVER_MESSAGE_WITH_FILE_RE = re.compile(
    r"Message\(kind='([^']+)',\s*message='((?:\\'|[^'])*)'[^)]*pos=Position\(line=(\d+)[^)]*file='([^']*)'"
)


def iter_isabelle_server_error_messages(
    output: str,
    *,
    file_filter: Optional[str] = None,
) -> List[Tuple[str, int, str]]:
    """
    从 Isabelle server 输出解析 kind='error' 的 Message。
    返回 [(message, line_no, file_path), ...]；忽略 writeln/warning 等信息性消息。
    """
    if not output:
        return []
    found: List[Tuple[str, int, str]] = []
    for m in _ISABELLE_SERVER_MESSAGE_WITH_FILE_RE.finditer(output):
        kind = m.group(1)
        if kind not in _ISABELLE_ERROR_MESSAGE_KINDS:
            continue
        msg = m.group(2).replace("\\'", "'")
        line_no = int(m.group(3))
        fpath = m.group(4).replace("\\", "/")
        if file_filter:
            name = Path(file_filter.replace("\\", "/")).name
            stem = Path(name).stem
            if name not in fpath and stem not in fpath:
                continue
        found.append((msg, line_no, fpath))
    return found


def _to_cygwin_path(path: str) -> str:
    path_str = str(path).replace("\\", "/")
    if len(path_str) > 1 and path_str[1] == ":":
        drive = path_str[0].lower()
        path_str = f"/cygdrive/{drive}{path_str[2:]}"
    return path_str


def _master_dir_for_theory(theory_dir: Path) -> str:
    try:
        rel = theory_dir.resolve().relative_to(Path.cwd().resolve())
        return str(rel).replace("\\", "/") or "."
    except ValueError:
        return _to_cygwin_path(str(theory_dir.absolute()))


def _extract_session_id(start_responses: Any) -> Optional[str]:
    if isinstance(start_responses, str):
        return start_responses
    if isinstance(start_responses, list):
        for item in reversed(start_responses):
            body = getattr(item, "response_body", None)
            sid = getattr(body, "session_id", None)
            if sid:
                return str(sid)
    return None


_TRANSIENT_ISABELLE_SERVER_ERRORS = (
    "Timer already cancelled",
    "IllegalStateException: Timer",
    "WinError 64",
    "WinError 1225",
    "指定的网络名不再可用",
    "远程计算机拒绝网络连接",
    "Server 模式异常",
    "Server 复用池未初始化",
)


def _is_transient_isabelle_server_error(output: str) -> bool:
    """Isabelle server 长跑/频繁重启后的瞬态基础设施错误（非证明逻辑失败）。"""
    text = output or ""
    return any(frag in text for frag in _TRANSIENT_ISABELLE_SERVER_ERRORS)


def _merge_server_responses(responses: Any) -> Tuple[int, str]:
    if not responses:
        return 1, "Server 模式响应为空"

    lines: List[str] = []
    ok = False
    for resp in responses:
        rtype = getattr(resp, "response_type", "UNKNOWN")
        rvalue = getattr(rtype, "value", None) or str(rtype)
        body = getattr(resp, "response_body", "")
        body_text = str(body)
        lines.append(f"[{str(rvalue).upper()}]")
        lines.append(body_text)
        if str(rvalue).upper() == "FINISHED":
            bdict = getattr(body, "model_dump", None)
            if callable(bdict):
                data = bdict()
                ok = bool(data.get("ok", False))
            elif isinstance(body, dict):
                ok = bool(body.get("ok", False))
    merged = "\n".join(lines)
    return (0 if ok else 1), merged


class IsabelleServerSessionPool:
    """
    单次定理后处理内复用同一 Isabelle server 与 session，避免每轮 use_theories 冷启动。
    """

    def __init__(self, config: IsabelleRunnerConfig):
        self.config = config
        self._client: Any = None
        self._session_id: Optional[str] = None
        self._server_proc: Any = None
        self._active = False
        self._thy_stale = False
        self._thy_loaded_in_session = False
        self._thy_seen_in_session = False
        self._thy_fingerprints: Dict[str, str] = {}
        self._loaded_theories: Set[str] = set()

    def mark_thy_stale(self) -> None:
        """标记 .thy 已在磁盘上修改，下次 use_theories 前需 purge 或重启 session。"""
        self._thy_stale = True

    def restart_session_if_stale(self, thy_path: Optional[Path] = None) -> bool:
        """兼容旧调用：委托 refresh_session_if_stale。"""
        if thy_path is None:
            return False
        return self.refresh_session_if_stale(thy_path)

    def refresh_session_if_stale(self, thy_path: Path) -> bool:
        """.thy 已修改时先 purge_theories，失败再回退 session 全量重启。"""
        if not self._thy_stale:
            return False
        if self._purge_loaded_theories(thy_path):
            return True
        self.restart_session()
        return True

    def _purge_loaded_theories(self, thy_path: Path) -> bool:
        if not self._active or not self._client or not self._session_id:
            return False
        if not (
            self._thy_loaded_in_session or self._thy_seen_in_session
        ):
            self._thy_stale = False
            return True
        master_dir = _master_dir_for_theory(thy_path.parent)
        theories = _theories_to_purge_for(thy_path, self._loaded_theories)
        try:
            self._client.purge_theories(
                self._session_id,
                theories,
                master_dir=master_dir,
                purge_all=True,
            )
            self._thy_stale = False
            self._thy_loaded_in_session = False
            self._thy_seen_in_session = False
            self._loaded_theories.clear()
            print(
                f"[isabelle_server] 已 purge theories（免重启）: {theories}",
                flush=True,
            )
            return True
        except Exception as exc:
            msg = f"[isabelle_server] purge_theories 失败，回退 session 重启: {exc}"
            print(msg, flush=True)
            logger.warning(msg)
            return False

    @property
    def is_active(self) -> bool:
        return self._active

    def __enter__(self) -> "IsabelleServerSessionPool":
        if self.config.use_server:
            self._start()
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    def _start(self) -> None:
        if self._active:
            return
        try:
            import nest_asyncio
            from isabelle_client import get_isabelle_client, start_isabelle_server
        except Exception as exc:
            raise RuntimeError(f"Server 模式不可用（缺少依赖）: {exc}") from exc

        nest_asyncio.apply()
        print("[isabelle_server] 正在启动 Isabelle server（本定理后处理内复用）...", flush=True)
        _server_info, server_proc = start_isabelle_server()
        self._server_proc = server_proc
        register_server_pid(getattr(server_proc, "pid", None))
        self._client = get_isabelle_client(_server_info)
        session_id = _extract_session_id(self._client.session_start())
        if not session_id:
            self.close()
            raise RuntimeError("Server 模式未获取 session_id")
        self._session_id = session_id
        self._active = True
        register_pool(self)
        print(f"[isabelle_server] session 已就绪: {session_id}", flush=True)

    def restart_session(self, *, fresh_server: bool = True) -> None:
        """
        修改 .thy 后必须重启 session，否则 PIDE 缓存会导致 sledgehammer 不再输出 Try this。

        Isabelle2025 server 的全局 Event_Timer 会被上一轮 use_theories 残留的周期性
        check_progress 任务拖死；一旦触发，后续调用会永久返回
        ``Timer already cancelled`` 或直接挂起。只做 session_stop/session_start
        无法恢复，因此默认整进程重启。
        """
        if not self._active or not self._client:
            return
        if fresh_server:
            self.restart_server()
            return
        old_sid = self._session_id
        if old_sid:
            if not _stop_isabelle_session(
                self._client, old_sid, context="重启前释放旧 session"
            ):
                self.force_abort_inflight_and_restart()
                return
            if SESSION_RESTART_DELAY_SEC > 0:
                print(
                    f"[isabelle_server] 等待 {SESSION_RESTART_DELAY_SEC}s 后再重启 session...",
                    flush=True,
                )
                time.sleep(SESSION_RESTART_DELAY_SEC)
        new_sid = _extract_session_id(self._client.session_start())
        if not new_sid:
            print(
                "[isabelle_server] session_start 返回空，尝试强制重启 server ...",
                flush=True,
            )
            self.force_abort_inflight_and_restart()
            if not self._session_id:
                raise RuntimeError("Isabelle server session 重启失败")
            return
        self._session_id = new_sid
        self._thy_stale = False
        self._thy_loaded_in_session = False
        self._thy_seen_in_session = False
        self._thy_fingerprints.clear()
        self._loaded_theories.clear()
        if old_sid:
            print(
                f"[isabelle_server] session 已重启: {old_sid} → {new_sid}",
                flush=True,
            )
        else:
            print(f"[isabelle_server] session 已重启: {new_sid}", flush=True)

    def force_abort_inflight_and_restart(
        self,
        *,
        worker_thread: Optional[threading.Thread] = None,
    ) -> None:
        """
        wall-clock 超时且后台 worker 仍阻塞在 use_theories 时：
        直接终止 server 子进程（不对同一 client 并发 asyncio.run/session_stop），
        等待 worker 结束后再拉起新 server/session。
        """
        if not self._active:
            return
        old_sid = self._session_id
        print(
            "[isabelle_server] 强制终止卡住的 Isabelle server（避免 asyncio 死锁）...",
            flush=True,
        )
        from .isabelle_server_lifecycle import (
            _kill_windows_isabelle_orphans,
            _terminate_subprocess,
        )

        # 禁止 session_stop：worker 线程可能正占用同一 client 的 asyncio 循环
        _terminate_subprocess(self._server_proc)
        self._client = None
        self._session_id = None
        self._server_proc = None
        self._thy_stale = False
        self._thy_loaded_in_session = False
        self._thy_seen_in_session = False
        self._thy_fingerprints.clear()
        self._loaded_theories.clear()
        self._active = False

        if worker_thread is not None and worker_thread.is_alive():
            worker_thread.join(timeout=WORKER_DRAIN_AFTER_FORCE_KILL_SEC)
            if worker_thread.is_alive():
                print(
                    "[isabelle_server] 警告: use_theories worker 未在 "
                    f"{WORKER_DRAIN_AFTER_FORCE_KILL_SEC}s 内结束，继续重启 session ...",
                    flush=True,
                )

        if self.config.kill_orphan_poly_on_shutdown:
            n = _kill_windows_isabelle_orphans(aggressive=True)
            if n:
                print(
                    f"[isabelle_server] 已结束遗留 worker（{n} 类进程镜像）",
                    flush=True,
                )

        if SESSION_RESTART_DELAY_SEC > 0:
            print(
                f"[isabelle_server] 等待 {SESSION_RESTART_DELAY_SEC}s 后再重启 session...",
                flush=True,
            )
            time.sleep(SESSION_RESTART_DELAY_SEC)

        self._start()
        if old_sid and self._session_id:
            print(
                f"[isabelle_server] session 已强制重启: {old_sid} → {self._session_id}",
                flush=True,
            )

    def restart_server(self) -> None:
        """直接重启 Isabelle **server 进程**（不只是 session）。

        hammer 被 watchdog 取消后，server 侧的 PIDE 计时器可能已失效并持续返回
        ``Timer already cancelled``；此时仅重启 session 无法恢复，必须换新进程。
        """
        if not self._active:
            return
        from .isabelle_server_lifecycle import (
            _kill_windows_isabelle_orphans,
            _terminate_subprocess,
        )

        old_sid = self._session_id
        print(
            "[isabelle_server] 重启整个 Isabelle server（清空 PIDE / Event_Timer 状态）...",
            flush=True,
        )
        _terminate_subprocess(self._server_proc)
        self._client = None
        self._session_id = None
        self._server_proc = None
        self._active = False
        self._thy_stale = False
        self._thy_loaded_in_session = False
        self._thy_seen_in_session = False
        self._thy_fingerprints.clear()
        self._loaded_theories.clear()
        if self.config.kill_orphan_poly_on_shutdown:
            n = _kill_windows_isabelle_orphans(aggressive=True)
            if n:
                print(
                    f"[isabelle_server] 已结束遗留 worker（{n} 类进程镜像）",
                    flush=True,
                )
        if SESSION_RESTART_DELAY_SEC > 0:
            time.sleep(SESSION_RESTART_DELAY_SEC)
        self._start()
        if old_sid and self._session_id:
            print(
                f"[isabelle_server] session 已重启: {old_sid} → {self._session_id}",
                flush=True,
            )

    def close(self, *, kill_orphans: Optional[bool] = None) -> None:
        was_active = self._active
        try:
            if self._client and self._session_id:
                _stop_isabelle_session(
                    self._client, self._session_id, context="关闭复用 pool"
                )
            if self._client:
                try:
                    self._client.shutdown()
                except Exception:
                    pass
            from .isabelle_server_lifecycle import _terminate_subprocess

            _terminate_subprocess(self._server_proc)
        finally:
            self._client = None
            self._session_id = None
            self._server_proc = None
            self._active = False
            self._thy_stale = False
            self._thy_loaded_in_session = False
            self._thy_seen_in_session = False
            self._thy_fingerprints.clear()
            self._loaded_theories.clear()
            unregister_pool(self)
            if was_active:
                print("[isabelle_server] 已关闭复用 session", flush=True)
            if kill_orphans is None:
                kill_orphans = self.config.kill_orphan_poly_on_shutdown
            if kill_orphans:
                from .isabelle_server_lifecycle import _kill_windows_isabelle_orphans

                n = _kill_windows_isabelle_orphans(aggressive=True)
                if n:
                    print(
                        f"[isabelle_server] 已结束遗留 worker（{n} 类进程镜像）",
                        flush=True,
                    )

    def use_theories(
        self,
        theories: List[str],
        master_dir: str,
        *,
        watchdog_timeout: Optional[int] = None,
    ) -> Any:
        if not self._active or not self._client or not self._session_id:
            raise RuntimeError("Server 复用池未初始化")
        kwargs: dict = {
            "theories": theories,
            "master_dir": master_dir,
            "session_id": self._session_id,
        }
        if watchdog_timeout is not None:
            kwargs["watchdog_timeout"] = watchdog_timeout
        return self._client.use_theories(**kwargs)

    def run_use_thy(
        self,
        thy_path: Path,
        tag: str,
        *,
        watchdog_timeout: Optional[int] = None,
    ) -> Tuple[int, str]:
        if not self._active or not self._client or not self._session_id:
            return 1, "Server 复用池未初始化"
        # .thy 已在磁盘修改后 purge（优先）或重启 session，避免 PIDE 缓存导致误报
        fingerprint = _thy_file_fingerprint(thy_path)
        if fingerprint:
            key = str(thy_path)
            previous = self._thy_fingerprints.get(key)
            if previous is not None and previous != fingerprint:
                self.mark_thy_stale()
            self._thy_fingerprints[key] = fingerprint
        self.refresh_session_if_stale(thy_path)
        theory_name = thy_path.stem
        master_dir = _master_dir_for_theory(thy_path.parent)
        wd = watchdog_timeout if watchdog_timeout is not None else self.config.timeout
        max_attempts = 2
        last_code, last_out = 1, ""
        for attempt in range(1, max_attempts + 1):
            try:
                responses = self._client.use_theories(
                    theories=[theory_name],
                    master_dir=master_dir,
                    watchdog_timeout=wd,
                    session_id=self._session_id,
                )
                last_code, last_out = _merge_server_responses(responses)
            except Exception as exc:
                last_code, last_out = 1, f"Server 模式异常 ({tag}): {exc}"

            if last_code == 0 or not _is_transient_isabelle_server_error(last_out):
                break
            if attempt < max_attempts:
                print(
                    f"[isabelle_server] {tag} 遇到瞬态 server 错误，"
                    f"重启 server 进程并重试 ({attempt}/{max_attempts - 1}) ...",
                    flush=True,
                )
                self.restart_server()
                self.mark_thy_stale()
                continue
            print(
                f"[isabelle_server] {tag} server 模式连续瞬态错误，"
                "回退 CLI 进程验证（隔离 server 计时器状态）...",
                flush=True,
            )
            return _run_use_thy_cli(thy_path, self.config, tag)

        self._thy_seen_in_session = True
        if last_code == 0:
            self._thy_loaded_in_session = True
            self._loaded_theories.update(_theories_to_purge_for(thy_path))
        return last_code, last_out


_ISABELLE_IMPORT_PACKAGES = frozenset(
    {"Main", "HOL", "Complex", "Groups", "Lin_Arith", "Set", "Relation"}
)


def _import_theory_names_from_thy_header(text: str) -> List[str]:
    """从 .thy 头部 imports 行解析全部理论名（引号路径 + 无引号名称）。"""
    from ..lemma.thy_imports import import_theory_name_from_path

    names: List[str] = []
    header = (text or "").split("begin", 1)[0]
    for line in header.splitlines():
        m = re.match(r"^\s*imports\s+(.*)$", line, re.IGNORECASE)
        if not m:
            continue
        tail = m.group(1)
        for q in re.finditer(r'"([^"]+)"', tail):
            name = import_theory_name_from_path(q.group(1))
            if name:
                names.append(name)
        tail_no_quotes = re.sub(r'"[^"]*"', " ", tail)
        for part in tail_no_quotes.split():
            token = part.strip()
            if not token or token in _ISABELLE_IMPORT_PACKAGES:
                continue
            names.append(token)
    return names


def _thy_file_fingerprint(thy_path: Path) -> str:
    """Content fingerprint of a .thy file; a change invalidates the session snapshot."""
    try:
        return hashlib.sha1(thy_path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _theories_to_purge_for(
    thy_path: Path,
    extra: Optional[Set[str]] = None,
) -> List[str]:
    """收集主理论及 imports 引用的理论名，供 purge_theories 使用。"""
    names: List[str] = [thy_path.stem]
    try:
        text = thy_path.read_text(encoding="utf-8")
        names.extend(_import_theory_names_from_thy_header(text))
    except OSError:
        pass
    if extra:
        names.extend(extra)
    seen: Set[str] = set()
    ordered: List[str] = []
    for n in names:
        if n not in seen:
            seen.add(n)
            ordered.append(n)
    return ordered


def reload_theories_from_disk(
    thy_paths: Sequence[Path],
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
    *,
    label: str = "domain",
) -> bool:
    """
    磁盘上的 .thy 更新后，以其所在目录为 master_dir 执行 purge + use_theories。

    final 验证时 purge 列表以定理目录为 master_dir，无法清除在
    ../<domain>/proven_lemmas 下加载的旧 session 缓存；须在领域目录下显式重载。
    """
    if server_pool is None or not server_pool.is_active:
        return True
    all_ok = True
    for thy_path in thy_paths:
        if not thy_path.is_file():
            continue
        server_pool.mark_thy_stale()
        server_pool.refresh_session_if_stale(thy_path)
        code, out = server_pool.run_use_thy(
            thy_path,
            tag=f"reload_{label}_{thy_path.stem}",
            watchdog_timeout=config.verify_timeout,
        )
        if code != 0:
            all_ok = False
            logger.warning(
                "重载 %s 失败 (rc=%s): %s",
                thy_path,
                code,
                (out or "")[:800],
            )
            print(
                f"[isabelle_server] 重载 {thy_path.name} 失败，见日志",
                flush=True,
            )
        else:
            print(
                f"[isabelle_server] 已从磁盘重载: {thy_path}",
                flush=True,
            )
    return all_ok


def reload_domain_theories_after_proven_merge(
    proven_path: Path,
    defs_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
) -> bool:
    """merge 写入领域 proven/defs 后，在各自 master_dir 下重载。"""
    paths: List[Path] = []
    if defs_path.is_file():
        paths.append(defs_path)
    if proven_path.is_file():
        paths.append(proven_path)
    if not paths:
        return True
    print(
        "\n[proven-lemmas] 正在重载领域 defs / proven_lemmas（供 final 验证使用）...",
        flush=True,
    )
    return reload_theories_from_disk(
        paths,
        config,
        server_pool,
        label="domain",
    )


def prepare_session_for_repair_sledgehammer(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """
    repair 轮次跑 sledgehammer 前重启 session。

    purge 无法清掉 PIDE 缓存；长跑后 server 模式 hammer 常不输出 Try this。
    """
    if server_pool is None or not server_pool.is_active:
        return
    print(
        "[repair] 重启 Isabelle session（sledgehammer 定向修复前）...",
        flush=True,
    )
    server_pool.restart_session()


def prepare_session_for_lemma_proof_verify(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """
    引理 LLM 写入 .thy 后验证前重启 session，避免 PIDE 缓存误报通过。
    """
    if server_pool is None or not server_pool.is_active:
        return
    print(
        "[lemma-proof] 重启 Isabelle session（引理验证前）...",
        flush=True,
    )
    server_pool.restart_session()


def prepare_session_for_lemma_llm_repair(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """
    sledgehammer 定向修复失败后、LLM 修复轮次开始前重启 session，
    终止可能仍在后台运行的 hammer 并清空 PIDE 缓存。
    """
    if server_pool is None or not server_pool.is_active:
        return
    print(
        "[lemma-proof] 重启 Isabelle session（LLM 修复前）...",
        flush=True,
    )
    server_pool.restart_session()


def prepare_session_for_repair_final_verify(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """
    repair 回填后最终验证前重启 session。

    repair 轮次会改写 .thy 并在 session 内跑 hammer；仅 purge 时 repair_final_verify
    仍可能用旧 PIDE 缓存，导致磁盘上正确的证明被判失败。
    """
    if server_pool is None or not server_pool.is_active:
        return
    print(
        "[repair] 重启 Isabelle session（repair 后最终验证前）...",
        flush=True,
    )
    server_pool.restart_session()


def prepare_session_for_repair_refresh_verify(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """
    定向 repair 每轮回填后 re-verify 前重启 session，刷新 Isabelle 报错行号。
    """
    if server_pool is None or not server_pool.is_active:
        return
    print(
        "[repair] 重启 Isabelle session（刷新报错行 verify 前）...",
        flush=True,
    )
    server_pool.restart_session()


def verify_domain_proven_lemmas_after_merge(
    proven_path: Path,
    defs_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
) -> Tuple[bool, str]:
    """
    merge 写入 proven_lemmas.thy 后：重启 session，依次加载 defs → proven 并严格验证。
    """
    if server_pool is None or not server_pool.is_active:
        return True, ""
    if not proven_path.is_file():
        return True, ""

    print(
        "\n[proven-lemmas] merge 后全量验证 defs / proven_lemmas ...",
        flush=True,
    )
    server_pool.restart_session()
    last_out = ""
    if defs_path.is_file():
        code, last_out = server_pool.run_use_thy(
            defs_path,
            "merge_verify_defs",
            watchdog_timeout=config.verify_timeout,
        )
        if not _verification_passed(code, last_out):
            print(
                f"[proven-lemmas] merge 后验证 {defs_path.name} 失败，见日志",
                flush=True,
            )
            logger.warning(
                "merge 后验证 %s 失败 (rc=%s): %s",
                defs_path,
                code,
                (last_out or "")[:800],
            )
            return False, last_out

    code, last_out = server_pool.run_use_thy(
        proven_path,
        "merge_verify_proven",
        watchdog_timeout=config.verify_timeout,
    )
    ok = _verification_passed(code, last_out)
    if ok:
        print("[proven-lemmas] merge 后全量验证通过", flush=True)
    else:
        print(
            f"[proven-lemmas] merge 后验证 {proven_path.name} 失败，见日志",
            flush=True,
        )
        logger.warning(
            "merge 后验证 %s 失败 (rc=%s): %s",
            proven_path,
            code,
            (last_out or "")[:800],
        )
    return ok, last_out


def prepare_session_for_final_theory_verify(
    proven_path: Path,
    defs_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
) -> bool:
    """
    final .thy 验证前：重启 session 并按 defs → proven 顺序从磁盘重载。

    长跑中 sketch/unproven 阶段会在 session 里加载旧版 proven_lemmas；
    仅 purge 无法清掉跨 master_dir 的缓存，final 会报 Undefined fact（磁盘文件已更新）。
    """
    if server_pool is None or not server_pool.is_active:
        return True

    print(
        "\n[final-theory] 重启 Isabelle session 并重载领域 defs / proven_lemmas ...",
        flush=True,
    )
    if server_pool._thy_loaded_in_session or server_pool._loaded_theories:
        server_pool.restart_session()

    paths: List[Path] = []
    if defs_path.is_file():
        paths.append(defs_path)
    if proven_path.is_file():
        paths.append(proven_path)
    if not paths:
        return True
    return reload_theories_from_disk(
        paths,
        config,
        server_pool,
        label="final_prep",
    )


def prepare_session_for_self_contained_verify(
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
) -> bool:
    """
    自包含 final .thy 验证前：重启 session，不预载自定义引理库。

    自包含定理文件内联了定义与所引用引理、只 imports Main，故预载领域
    defs / proven_lemmas 会掩盖"内联是否完整"，这里必须用干净 session 验证。
    """
    if server_pool is None or not server_pool.is_active:
        return True
    if server_pool._thy_loaded_in_session or server_pool._loaded_theories:
        print(
            "\n[final-theory] 重启 Isabelle session（自包含验证，不预载引理库）...",
            flush=True,
        )
        server_pool.restart_session()
    return True


def _has_sledgehammer_lines(thy_path: Path) -> bool:
    try:
        text = thy_path.read_text(encoding="utf-8")
    except OSError:
        return False
    return bool(_SLEDGEHAMMER_LINE.search(text))


def _watchdog_for_tag(config: IsabelleRunnerConfig, tag: str) -> int:
    if tag.startswith("sledgehammer_round") or tag.startswith("repair_round_"):
        return config.timeout
    return config.verify_timeout


def _uses_verify_wall_clock(tag: str) -> bool:
    """是否对该 tag 启用 wall-clock 硬超时（对应 jEdit 紫色长时间不返回）。"""
    if tag.startswith(
        (
            "verify",
            "lemma_proof",
            "lemma_single_verify",
            "repair_final_verify",
            "repair_verify_",
            "final_",
        )
    ):
        return True
    return tag in ("standalone",)


def _uses_sledgehammer_wall_clock(tag: str) -> bool:
    """sledgehammer 等待 Try this 的 wall-clock 硬超时（默认与 config.timeout 一致，60s）。"""
    return tag.startswith(
        ("repair_round_", "stuck_repair_round_", "sledgehammer_round_")
    )


def _wall_timeout_for_tag(config: IsabelleRunnerConfig, tag: str) -> Optional[int]:
    if _uses_verify_wall_clock(tag):
        return config.verify_wall_timeout_sec
    if _uses_sledgehammer_wall_clock(tag):
        return config.sledgehammer_wall_timeout_sec
    return None


def _is_stuck_verify_output(output: str) -> bool:
    return STUCK_VERIFY_MARKER in (output or "")


def _stuck_verify_is_likely_load_stall(output: str) -> bool:
    """STUCK_VERIFY 且无 Isabelle 证明/语法报错 → 多为大 theory 加载超时，不应 stuck-repair。"""
    if not _is_stuck_verify_output(output):
        return False
    text = output or ""
    proof_failure_markers = (
        "Failed to finish proof",
        "Failed to apply initial proof method",
        "Undefined case",
        "Illegal application",
        "Undefined fact",
        "error:",
        "***",
        "Unbound",
        "Type unification failed",
    )
    return not any(m in text for m in proof_failure_markers)


def _stuck_verify_message(tag: str, elapsed_sec: int) -> str:
    return (
        f"{STUCK_VERIFY_MARKER} wall-clock timeout after {elapsed_sec}s ({tag}); "
        "Isabelle 可能仍在后台计算该证明步（jEdit 紫色状态）"
    )


def _on_verify_wall_timeout(
    server_pool: Optional[IsabelleServerSessionPool],
    tag: str,
    *,
    worker_thread: Optional[threading.Thread] = None,
) -> None:
    print(
        f"[isabelle] {tag} wall-clock 超时，重启 session 以终止卡住的证明 ...",
        flush=True,
    )
    if server_pool is None or not server_pool.is_active:
        return
    if worker_thread is not None and worker_thread.is_alive():
        server_pool.force_abort_inflight_and_restart(worker_thread=worker_thread)
    else:
        server_pool.restart_session()


def _run_blocking_with_heartbeat(
    fn: Callable[[], Tuple[int, str]],
    tag: str,
    *,
    heartbeat_sec: int,
    max_wall_sec: Optional[int] = None,
    on_wall_timeout: Optional[Callable[[threading.Thread], None]] = None,
) -> Tuple[int, str]:
    if heartbeat_sec <= 0 and max_wall_sec is None:
        return fn()
    holder: List[Optional[Tuple[int, str]]] = [None]
    err: List[Optional[BaseException]] = [None]
    done = threading.Event()

    def _worker() -> None:
        try:
            holder[0] = fn()
        except BaseException as exc:
            err[0] = exc
        finally:
            done.set()

    worker = threading.Thread(target=_worker, daemon=True)
    worker.start()
    start = time.monotonic()
    while not done.wait(timeout=heartbeat_sec if heartbeat_sec > 0 else 1):
        elapsed = int(time.monotonic() - start)
        print(
            f"[isabelle] {tag} 仍在等待 Isabelle ... {elapsed}s",
            flush=True,
        )
        if max_wall_sec is not None and elapsed >= max_wall_sec:
            if on_wall_timeout is not None:
                on_wall_timeout(worker)
            elif worker.is_alive():
                worker.join(timeout=WORKER_DRAIN_AFTER_FORCE_KILL_SEC)
            return 1, _stuck_verify_message(tag, elapsed)
    if err[0] is not None:
        raise err[0]
    assert holder[0] is not None
    return holder[0]


def _run_use_thy(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    tag: str,
    server_pool: Optional[IsabelleServerSessionPool] = None,
    *,
    watchdog_timeout: Optional[int] = None,
    wall_timeout: Optional[int] = None,
) -> Tuple[int, str]:
    wd = watchdog_timeout if watchdog_timeout is not None else _watchdog_for_tag(config, tag)

    def _call() -> Tuple[int, str]:
        ensure_thy_single_closure(thy_path, server_pool=server_pool)
        if config.use_server:
            if server_pool is not None and server_pool.is_active:
                return server_pool.run_use_thy(thy_path, tag, watchdog_timeout=wd)
            return _run_use_thy_server(thy_path, config)
        return _run_use_thy_cli(thy_path, config, tag)

    if config.use_server and server_pool is not None and server_pool.is_active:
        wall = (
            wall_timeout
            if wall_timeout is not None
            else _wall_timeout_for_tag(config, tag)
        )
        return _run_blocking_with_heartbeat(
            _call,
            tag,
            heartbeat_sec=config.use_theories_heartbeat_sec,
            max_wall_sec=wall,
            on_wall_timeout=(
                (lambda worker: _on_verify_wall_timeout(server_pool, tag, worker_thread=worker))
                if wall
                else None
            ),
        )
    return _call()


def _run_use_thy_cli(thy_path: Path, config: IsabelleRunnerConfig, tag: str) -> Tuple[int, str]:
    theory_dir = thy_path.parent
    theorem_name = thy_path.stem
    env = os.environ.copy()
    env = {k: str(v) for k, v in env.items() if v is not None}
    env["ISABELLE_HOME"] = str(config.isabelle_home)
    theory_dir_cygwin = _to_cygwin_path(str(theory_dir.absolute()))
    script_content = f"""#!/bin/bash
cd "{theory_dir_cygwin}"
$ISABELLE_HOME/bin/isabelle process -o quick_and_dirty=true -l HOL -e 'use_thy "{theorem_name}"'
"""
    script_path = theory_dir / f"_{tag}.sh"
    with open(script_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(script_content)
    script_cygwin = _to_cygwin_path(str(script_path.absolute()))
    cli_timeout = config.timeout
    wall = _wall_timeout_for_tag(config, tag)
    if wall is not None:
        cli_timeout = wall
    try:
        proc = subprocess.run(
            [str(Path(config.isabelle_path)), "-l", script_cygwin],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=cli_timeout,
            cwd=str(theory_dir),
            env=env,
        )
        merged = (proc.stdout or "") + ("\n" if proc.stdout and proc.stderr else "") + (proc.stderr or "")
        return proc.returncode, merged
    except subprocess.TimeoutExpired as exc:
        out_parts = []
        if exc.stdout:
            out_parts.append(exc.stdout if isinstance(exc.stdout, str) else exc.stdout.decode("utf-8", errors="replace"))
        if exc.stderr:
            out_parts.append(exc.stderr if isinstance(exc.stderr, str) else exc.stderr.decode("utf-8", errors="replace"))
        merged = "\n".join(out_parts)
        return 1, merged + "\n" + _stuck_verify_message(tag, cli_timeout)
    finally:
        if script_path.exists():
            script_path.unlink()


def _run_use_thy_server(thy_path: Path, config: IsabelleRunnerConfig) -> Tuple[int, str]:
    """单次调用：独立启动 server/session（无复用池时的回退路径）。"""
    try:
        with IsabelleServerSessionPool(config) as pool:
            return pool.run_use_thy(thy_path, "standalone")
    except RuntimeError as exc:
        return 1, str(exc)


def _normalize_tactic(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip())


def _clean_try_this_suggestion(raw: str) -> str:
    sug = (raw or "").strip()
    for sep in ("', pos=", ")), Message(", "], exports=", "')", '", pos='):
        if sep in sug:
            sug = sug.split(sep, 1)[0].strip()
    sug = re.sub(r"\s*\(\d+(?:\.\d+)?\s*ms\)\s*$", "", sug)
    if re.search(r"Message\(|Position\(|exports=|errors=", sug):
        return ""
    return sug


def _is_acceptable_tactic(sug: str) -> bool:
    return sug.startswith(("by ", "apply ", "using ", "unfolding "))


def _extract_try_this_by_line(output: str) -> dict[int, List[str]]:
    """从 server 输出按 Isabelle 行号收集 Try this 建议。"""
    result: dict[int, List[str]] = {}
    if not output:
        return result
    pattern = re.compile(
        r"Try this:\s*([^\n\r']+?)"
        r"(?:\s*\(\d+(?:\.\d+)?\s*ms\))?"
        r"['\"][^)]*?pos=Position\(line=(\d+)",
    )
    for m in pattern.finditer(output):
        sug = _clean_try_this_suggestion(m.group(1))
        if not sug or not _is_acceptable_tactic(sug):
            continue
        line = int(m.group(2))
        bucket = result.setdefault(line, [])
        if sug not in bucket:
            bucket.append(sug)
    if result:
        return result
    fallback: List[str] = []
    for m in re.finditer(r"Try this:\s*([^\n\r]+)", output or ""):
        sug = _clean_try_this_suggestion(m.group(1))
        if sug and _is_acceptable_tactic(sug):
            fallback.append(sug)
    if fallback:
        result[0] = fallback
    return result


def _extract_try_this_suggestions(
    output: str,
    *,
    line_no: Optional[int] = None,
) -> List[str]:
    by_line = _extract_try_this_by_line(output)
    if line_no is not None:
        return list(by_line.get(line_no, []))
    suggestions: List[str] = []
    seen: Set[str] = set()
    for ln in sorted(by_line):
        for sug in by_line[ln]:
            norm = _normalize_tactic(sug)
            if norm not in seen:
                seen.add(norm)
                suggestions.append(sug)
    return suggestions


_THEOREM_START_RE = re.compile(
    r"^\s*(theorem|lemma|corollary|proposition)\b", re.IGNORECASE
)
_BLOCK_BODY_RE = re.compile(r"^\s*(obtain|fix|assume)\b")
_METHOD_START_RE = re.compile(r"^\s*(proof|by|apply)\b")
_PROOF_END_RE = re.compile(r"^\s*(qed|next|end)\b")


def _ensure_proof_block_before_block_commands(text: str) -> Tuple[str, int]:
    """定理陈述后直接跟 obtain/fix/assume 时补 ``proof -``。

    ``obtain`` 等块命令不能直接出现在 prove mode；LLM 草图常漏掉
    ``proof -``，导致 ``Illegal application of proof command in "prove" mode``。
    已有的 ``qed`` 正好闭合补出的 proof 块。
    """
    lines = (text or "").splitlines()
    inserted = 0
    i = 0
    while i < len(lines):
        if not _THEOREM_START_RE.match(lines[i]):
            i += 1
            continue
        j = i + 1
        action = None
        while j < len(lines):
            stripped = lines[j].strip()
            if not stripped or stripped.startswith("(*"):
                j += 1
                continue
            if _METHOD_START_RE.match(lines[j]) or re.search(r"\bby\s+\S", lines[j]):
                action = "skip"
                break
            if _PROOF_END_RE.match(lines[j]):
                action = "skip"
                break
            if _BLOCK_BODY_RE.match(lines[j]):
                action = "insert"
                break
            if _THEOREM_START_RE.match(lines[j]):
                action = "skip"
                break
            j += 1
        if action == "insert":
            indent = re.match(r"^\s*", lines[j]).group(0) or "  "
            lines.insert(j, f"{indent}proof -")
            inserted += 1
            j += 1
        i = max(j, i + 1)
    return "\n".join(lines) + ("\n" if text.endswith("\n") else ""), inserted


def _sanitize_theory_before_verify(
    thy_path: Path,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> bool:
    """
    验证前语法清洗：
    - 统一换行与常见不可见字符
    - 将常见 Unicode 逻辑符号替换为 Isabelle ASCII 记法，降低词法错误概率
    """
    text = thy_path.read_text(encoding="utf-8")
    original = text
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    text = text.replace("\ufeff", "")
    text = text.replace("\u00a0", " ")
    text = text.replace("\u2007", " ")
    text = text.replace("\u202f", " ")
    # 常见 Unicode 逻辑符号 -> Isabelle ASCII
    replacements = {
        "⟷": "\\<longleftrightarrow>",
        "↔": "\\<longleftrightarrow>",
        "∧": "\\<and>",
        "∨": "\\<or>",
        "¬": "\\<not>",
        "→": "\\<longrightarrow>",
        "≤": "\\<le>",
        "≥": "\\<ge>",
        "≠": "\\<noteq>",
        "∈": "\\<in>",
        "∉": "\\<notin>",
    }
    for src, dst in replacements.items():
        text = text.replace(src, dst)
    # 将 Isar Unicode 注释（― ‹...›）转换为标准注释，避免 CLI 词法报错
    text = re.sub(r"^\s*―\s*‹(.*?)›\s*$", r"(* \1 *)", text, flags=re.MULTILINE)
    # 去掉 LLM 输出残留的 Markdown 代码围栏（如 qed``` / 独立 ```isabelle 行）
    text = re.sub(r"^[ \t]*```[A-Za-z0-9_+-]*[ \t]*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"```[ \t]*$", "", text, flags=re.MULTILINE)
    # 定理陈述后直接跟 obtain/fix/assume 时补 proof -
    text, _ = _ensure_proof_block_before_block_commands(text)

    # 先把内联行尾 sledgehammer 规范化为独立命令行，避免语法/模式错误
    lines = text.splitlines()
    normalized_lines: List[str] = []
    inline_pat = re.compile(r"^(?P<prefix>.*?)(?:\s+)sledgehammer(?:\s*\[[^\]]*\])?\s*$")
    for line in lines:
        m = inline_pat.match(line)
        # 仅处理“前面还有内容”的行尾 sledgehammer；独立 sledgehammer 保持不变
        if m and m.group("prefix").strip():
            prefix = m.group("prefix").rstrip()
            indent = re.match(r"^\s*", line).group(0)
            normalized_lines.append(prefix)
            normalized_lines.append(f"{indent}sledgehammer")
        else:
            normalized_lines.append(line)
    # 清除意外写入 .thy 的 server 响应对象尾巴（Message/Position/exports 等）
    cleaned_lines: List[str] = []
    cut_markers = (
        "', pos=Position(",
        '", pos=Position(',
        ", Message(kind=",
        "], exports=[])]",
        "], exports=[])",
    )
    for line in normalized_lines:
        cut_pos = None
        for marker in cut_markers:
            p = line.find(marker)
            if p >= 0:
                cut_pos = p if cut_pos is None else min(cut_pos, p)
        if cut_pos is not None:
            line = line[:cut_pos].rstrip()
        # 去掉建议里的耗时后缀：by simp (0.0 ms) -> by simp
        line = re.sub(r"\s+\(\d+(?:\.\d+)?\s*ms\)\s*$", "", line)
        # 清理残留孤立引号
        if line.endswith("'") and (" by " in line or line.strip().startswith("by ")):
            line = line[:-1].rstrip()
        cleaned_lines.append(line)
    text = "\n".join(cleaned_lines)

    changed = text != original
    if changed:
        thy_path.write_text(text + ("\n" if not text.endswith("\n") else ""), encoding="utf-8")
        ensure_thy_single_closure(thy_path, server_pool=server_pool)
    return changed


def _extract_error_positions(output: str) -> List[Tuple[int, str]]:
    """
    从 Isabelle 输出解析 (行号, 错误摘要)。
    支持 server Message(...) 与 CLI 文本两种格式。
    """
    if not output:
        return []
    found: List[Tuple[int, str]] = []

    for msg, line_no, _fpath in iter_isabelle_server_error_messages(output):
        found.append((line_no, msg))

    for m in re.finditer(
        r"Failed to finish proof \(line (\d+) of [^)]+\):\s*\n\*\*\* goal",
        output,
    ):
        found.append((int(m.group(1)), "Failed to finish proof"))

    for m in re.finditer(
        r"At command \"[^\"]+\" \(line (\d+) of [^)]+\)",
        output,
    ):
        found.append((int(m.group(1)), "At command"))

    for m in re.finditer(
        r"Failed to apply initial proof method \(line (\d+) of [^)]+\)",
        output,
    ):
        found.append((int(m.group(1)), "Failed to apply initial proof method"))

    # 去重保序（同行只保留第一条）
    seen: Set[int] = set()
    unique: List[Tuple[int, str]] = []
    for line_no, msg in found:
        if line_no in seen:
            continue
        seen.add(line_no)
        unique.append((line_no, msg))
    return unique


def _goal_signature(message: str) -> str:
    """把错误消息归一为“目标文本”签名，用于判断某一步是否真的闭合。

    只比较行号会被 use_thy 内部的行号位移误导（同一 goal 换行后仍失败却被判成功）。
    """
    text = (message or "").replace("\\n", "\n").replace("\\<^here>", "")
    has_goal = False
    for marker in ("goal (", "goal:"):
        idx = text.rfind(marker)
        if idx != -1:
            text = text[idx:]
            has_goal = True
            break
    if has_goal:
        # 有 goal 文本时按目标比较，行号无关；无线索时才退回行号。
        text = re.sub(r"\(line \d+ of [^)]*\)", "", text)
        text = re.sub(r"line=\d+", "", text)
    return re.sub(r"\s+", " ", text).strip()[:400]


def _error_signature_at_line(output: str, line_no: Optional[int]) -> Optional[str]:
    if line_no is None:
        return None
    for ln, msg in _extract_error_positions(output):
        if ln == line_no:
            return _goal_signature(msg)
    return None


_STRUCTURAL_ERROR_FRAGMENTS = (
    "Illegal theory header",
    "Cannot load theory",
)

_CASCADE_SYNTAX_FRAGMENTS = (
    "missing theory context",
)


def _summarize_error_positions(
    positions: List[Tuple[int, str]],
) -> Tuple[List[Tuple[int, str]], int]:
    """
    压缩连锁语法错误：end 后残留内容常触发 1 条根因 + 数十条 missing theory context。
    返回 (保留条目, 省略条数)。
    """
    if not positions:
        return [], 0

    structural = [
        (ln, msg)
        for ln, msg in positions
        if any(frag in msg for frag in _STRUCTURAL_ERROR_FRAGMENTS)
    ]
    if structural:
        kept: List[Tuple[int, str]] = []
        seen: Set[Tuple[int, str]] = set()
        suppressed = 0
        for ln, msg in positions:
            if any(frag in msg for frag in _CASCADE_SYNTAX_FRAGMENTS):
                suppressed += 1
                continue
            key = (ln, msg)
            if key in seen:
                continue
            seen.add(key)
            kept.append(key)
        # 结构类错误优先展示
        struct_keys = {(ln, msg) for ln, msg in structural}
        ordered = [item for item in kept if item in struct_keys]
        ordered.extend(item for item in kept if item not in struct_keys)
        return ordered, suppressed

    cascade = [item for item in positions if _CASCADE_SYNTAX_FRAGMENTS[0] in item[1]]
    if len(cascade) <= 1:
        return positions, 0

    kept_other = [item for item in positions if item not in cascade]
    return [cascade[0]] + kept_other, len(cascade) - 1


def ensure_thy_single_closure(
    thy_path: Path,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> bool:
    """
    规范化 theory begin…end 闭包：
    1) 丢弃第一个 end 之后的残留；
    2) 正文内移除多余 end，文件末尾保证恰好一个 end。
    """
    from .lemma_dedup import truncate_theory_to_first_closure
    from ..lemma.proven_lemma_store import ProvenLemmaStore

    try:
        raw = thy_path.read_text(encoding="utf-8")
    except OSError:
        return False
    trimmed = truncate_theory_to_first_closure(raw)
    normalized = ProvenLemmaStore.normalize_thy_text(trimmed)
    if normalized == raw:
        return False
    thy_path.write_text(normalized, encoding="utf-8")
    _mark_thy_disk_changed(server_pool)
    print(
        f"[thy] 已规范化 {thy_path.name}：保证单一 end 闭包",
        flush=True,
    )
    return True


def _is_repairable_proof_error(message: str) -> bool:
    return any(frag in message for frag in _REPAIRABLE_ERROR_FRAGMENTS)


def _is_sledgehammer_line(line: str) -> bool:
    return bool(re.search(r"\bsledgehammer(?:\s*\[[^\]]*\])?\s*$", line))


_SORRY_ONLY_LINE = re.compile(r"^\s*sorry\s*\.?\s*$", re.IGNORECASE)


def _is_sorry_closing_line(line: str) -> bool:
    return bool(_SORRY_ONLY_LINE.match(line))


def _find_hole_closing_sorry(lines: List[str], hammer_idx: int) -> Optional[int]:
    """返回 sledgehammer 洞后第一个非空行若为 sorry，则返回其下标。"""
    j = hammer_idx + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    if j < len(lines) and _is_sorry_closing_line(lines[j]):
        return j
    return None


def _drop_stale_sorry_above(lines: List[str], idx: int) -> Optional[int]:
    """删除紧贴在目标行上方的 sorry（上一轮补洞残留）。

    历史中间态可能写成 ``have ...`` / ``sorry`` / ``sledgehammer``；
    hammer 回填为真实方法后若不删除上方 sorry，会留下
    ``have ...`` / ``sorry`` / ``<method>`` 的非法序列。
    """
    j = idx - 1
    while j >= 0 and not lines[j].strip():
        j -= 1
    if j >= 0 and _is_sorry_closing_line(lines[j]):
        del lines[j]
        return j
    return None


def _suggestion_closes_goal(suggestion: str) -> bool:
    """判断一条 Try this 建议能否闭合目标（by ... / ... by ...）。"""
    t = _normalize_tactic(suggestion or "")
    if not t:
        return False
    if t.lower().startswith("by "):
        return True
    return bool(re.search(r"\bby\s+\S", t))


def _pick_closing_suggestion(suggestions: List[str]) -> Optional[str]:
    for sug in suggestions:
        if _suggestion_closes_goal(sug):
            return sug.strip()
    return None


def _ensure_holes_are_closed(
    thy_path: Path,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> int:
    """保证每个 sledgehammer 洞后面紧跟一条 sorry 闭合目标。

    sledgehammer 是诊断命令，不会关闭目标；若后面直接跟下一条证明命令，
    Isabelle 报 `Illegal application of proof command in "prove" mode`，
    Try this 输出也随文档报错一起丢失。旧版 BLProver 用
    `sledgehammer ... sorry` 正是为此。
    """
    try:
        lines = thy_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return 0
    inserted = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if _is_sledgehammer_line(line) and not line.lstrip().startswith("(*"):
            if _find_hole_closing_sorry(lines, i) is None:
                indent = re.match(r"^\s*", line).group(0)
                lines.insert(i + 1, f"{indent}sorry")
                inserted += 1
                i += 1
        i += 1
    if inserted:
        thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        ensure_thy_single_closure(thy_path, server_pool=server_pool)
        _mark_thy_disk_changed(server_pool)
    return inserted


def _find_single_sledgehammer_line(
    thy_path: Path, *, near_idx: Optional[int] = None
) -> Optional[int]:
    """返回文件中唯一的 sledgehammer 行下标；多处时取离 near_idx 最近的一处。

    清洗（ensure_thy_single_closure / 补 sorry）可能增删空行，导致
    ``_prepare_failed_step_for_sledgehammer`` 返回的下标失效。回填前必须
    重新定位，否则建议会被写到错误的行上，hammer 洞永远填不掉。
    """
    try:
        lines = thy_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    hits = [
        i
        for i, line in enumerate(lines)
        if _is_sledgehammer_line(line) and not line.lstrip().startswith("(*")
    ]
    if not hits:
        return None
    if len(hits) == 1 or near_idx is None:
        return hits[0]
    return min(hits, key=lambda i: abs(i - near_idx))


def _count_sledgehammer_holes(thy_path: Path) -> int:
    try:
        text = thy_path.read_text(encoding="utf-8")
    except OSError:
        return 0
    return sum(
        1
        for line in text.splitlines()
        if _is_sledgehammer_line(line) and not line.lstrip().startswith("(*")
    )


def _sledgehammer_round_wall(config: IsabelleRunnerConfig, holes: int) -> int:
    """按洞数给整轮 hammer 分配 wall-clock，避免 N 个目标共用 60s。"""
    per_hole = max(10, int(getattr(config, "sledgehammer_hole_timeout_sec", 30)))
    want = max(1, holes) * (per_hole + 5) + 40
    cap = max(60, int(getattr(config, "sledgehammer_round_max_wall_sec", 900)))
    return min(cap, max(config.timeout, want))


_INLINE_BY_RE = re.compile(r"\s+by\s+\S", re.IGNORECASE)


def _is_replaceable_proof_line(line: str) -> bool:
    stripped = line.strip()
    if not stripped or stripped.startswith("(*"):
        return False
    if _SKIP_LINE_HEAD.match(line):
        return False
    if _is_sledgehammer_line(line):
        return False
    if _PROOF_STEP_LINE.match(line):
        return True
    # 单行 ``have/show/... by tactic``：允许只替换 by 之后的证明方法，
    # 保留语句前缀（否则会丢掉后续步骤依赖的中间事实）。
    return bool(_INLINE_BY_RE.search(line))


def _resolve_proof_line_index(lines: List[str], error_line_1based: int) -> Optional[int]:
    """将 Isabelle 报错行映射到应修复的证明命令行（0-based）。"""
    if error_line_1based < 1 or error_line_1based > len(lines):
        return None
    idx = error_line_1based - 1
    if _is_sledgehammer_line(lines[idx]):
        return idx
    if _is_replaceable_proof_line(lines[idx]):
        return idx
    for j in range(idx, max(-1, idx - 6), -1):
        if _is_replaceable_proof_line(lines[j]):
            return j
    return None


def _is_premise_only_line(line: str, keyword: str) -> bool:
    """独立的 using / unfolding 前置行（证明在下一行）。"""
    stripped = line.strip()
    if not stripped.lower().startswith(keyword):
        return False
    if re.search(r"\bby\s+", line, re.IGNORECASE):
        return False
    if re.search(r"\s\.\s*$", line):
        return False
    return True


def _is_using_only_line(line: str) -> bool:
    return _is_premise_only_line(line, "using")


def _is_unfolding_only_line(line: str) -> bool:
    return _is_premise_only_line(line, "unfolding")


def _is_removable_premise_line(line: str) -> bool:
    return _is_using_only_line(line) or _is_unfolding_only_line(line)


def _sledgehammer_command(config: Optional[IsabelleRunnerConfig] = None) -> str:
    """构造实际写入 .thy 的 hammer 命令。

    显式 prover 列表可避免未激活的 prover（如 vampire）参与空等；
    ``timeout`` 限制单次搜索，避免"没响应"式 60s 空转。
    """
    provers = " ".join(
        p.strip() for p in str(getattr(config, "sledgehammer_provers", "") or "").split()
    )
    timeout = int(getattr(config, "sledgehammer_prover_timeout_sec", 0) or 0)
    opts: List[str] = []
    if provers:
        opts.append(f"prover={provers}")
    if timeout > 0:
        opts.append(f"timeout={timeout}")
    if not opts:
        return "sledgehammer"
    return f"sledgehammer [{', '.join(opts)}]"


def _prepare_failed_step_for_sledgehammer(
    lines: List[str],
    target_idx: int,
    *,
    hammer_cmd: str = "sledgehammer",
) -> Tuple[int, str]:
    """
    将失败证明步改为 sledgehammer。
    若上方有独立的 using / unfolding 前置行，则删除后与当前证明行合并为一行 sledgehammer。
    返回新的 target 行下标与可读日志。
    """
    removed: List[str] = []
    while target_idx > 0 and _is_removable_premise_line(lines[target_idx - 1]):
        removed.insert(0, lines[target_idx - 1].strip())
        del lines[target_idx - 1]
        target_idx -= 1

    old_proof = lines[target_idx]
    indent = re.match(r"^\s*", old_proof).group(0)
    stripped = old_proof.strip()

    # 单行 ``have h: "..." by simp`` / ``show ?thesis using h by auto``：
    # 只去掉 by 之后的证明方法，保留语句本身；sledgehammer 另起一行，
    # 由 _ensure_holes_are_closed 补 sorry 闭合当前目标。
    inline = _INLINE_BY_RE.search(old_proof)
    if inline and not stripped.lower().startswith(
        ("by ", "apply ", "using ", "unfolding ")
    ):
        prefix = old_proof[: inline.start()].rstrip()
        lines[target_idx] = prefix
        lines.insert(target_idx + 1, f"{indent}{hammer_cmd}")
        return (
            target_idx + 1,
            f"{old_proof.strip()!r} → 保留语句 {prefix.strip()!r}，"
            f"证明方法替换为 sledgehammer",
        )

    lines[target_idx] = f"{indent}{hammer_cmd}"

    if removed:
        return (
            target_idx,
            f"删除前置行 {len(removed)} 条: {removed!r}；"
            f"原证明 {old_proof.strip()!r} → sledgehammer（合并原 {len(removed) + 1} 行）",
        )
    return target_idx, f"{old_proof.strip()!r} → sledgehammer"


def _replace_first_sledgehammer_at_line(
    thy_path: Path,
    line_idx: int,
    suggestion: str,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> bool:
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    if line_idx < 0 or line_idx >= len(lines):
        return False
    line = lines[line_idx]
    if not re.search(r"\bsledgehammer(?:\s*\[[^\]]*\])?\s*$", line):
        return False
    suggestion = suggestion.strip()
    m = re.match(r"^(.*?)(?:\s*)sledgehammer(?:\s*\[[^\]]*\])?\s*$", line)
    prefix = (m.group(1) or "").rstrip() if m else ""
    if prefix:
        lines[line_idx] = f"{prefix} {suggestion}"
    else:
        indent = re.match(r"^\s*", line).group(0)
        lines[line_idx] = f"{indent}{suggestion}"
    if _suggestion_closes_goal(suggestion):
        sorry_idx = _find_hole_closing_sorry(lines, line_idx)
        if sorry_idx is not None:
            del lines[sorry_idx]
        _drop_stale_sorry_above(lines, line_idx)
    thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    ensure_thy_single_closure(thy_path, server_pool=server_pool)
    return True


def _pick_repair_target(
    lines: List[str],
    repairable: List[Tuple[int, str]],
    skipped_indices: Set[int],
    skipped_line_numbers: Set[int],
) -> Tuple[Optional[int], Optional[int]]:
    """从可修复错误中选取尚未跳过、且可替换的证明行（按行号升序，避免总卡在靠前错误）。"""
    for line_no, _msg in sorted(repairable, key=lambda x: x[0]):
        if line_no in skipped_line_numbers:
            continue
        idx = _resolve_proof_line_index(lines, line_no)
        if idx is None or idx in skipped_indices:
            continue
        return line_no, idx
    return None, None


_SLOW_TACTIC_PATTERNS: Tuple[re.Pattern[str], ...] = (
    re.compile(r"\bby\s+auto\b", re.IGNORECASE),
    re.compile(r"\bby\s+blast\b", re.IGNORECASE),
    re.compile(r"\bmetis\b", re.IGNORECASE),
    re.compile(r"\bby\s+fastforce\b", re.IGNORECASE),
    re.compile(r"\bby\s+simp\b", re.IGNORECASE),
)


def _stuck_tactic_priority(line: str) -> int:
    for pri, pat in enumerate(_SLOW_TACTIC_PATTERNS):
        if pat.search(line):
            return pri
    return len(_SLOW_TACTIC_PATTERNS)


def _line_has_by_tactic(line: str) -> bool:
    """含 by tactic 的可替换证明行（含 show ... by）。"""
    if _is_replaceable_proof_line(line):
        return True
    if _is_sledgehammer_line(line) or _SKIP_LINE_HEAD.match(line):
        return False
    if line.strip().startswith("(*"):
        return False
    return bool(re.search(r"\bby\s+\S", line))


def _pick_stuck_repair_target(
    lines: List[str],
    skipped_indices: Set[int],
) -> Optional[int]:
    """
    verify wall-clock 超时且无明确报错行时，按启发式选取可能卡住的证明行。
    优先 by auto / blast / metis 等易长时间运行的 tactic。
    """
    candidates: List[Tuple[int, int]] = []
    for i, line in enumerate(lines):
        if i in skipped_indices or not _line_has_by_tactic(line):
            continue
        candidates.append((_stuck_tactic_priority(line), i))
    if not candidates:
        for i, line in enumerate(lines):
            if i not in skipped_indices and _line_has_by_tactic(line):
                return i
        return None
    candidates.sort(key=lambda x: (x[0], x[1]))
    return candidates[0][1]


def _has_unmapped_repairable_errors(
    lines: List[str],
    repairable: List[Tuple[int, str]],
    skipped_line_numbers: Set[int],
) -> bool:
    """是否存在尚未跳过、但无法映射到证明命令行的报错行（需 re-verify 刷新）。"""
    for line_no, _msg in repairable:
        if line_no in skipped_line_numbers:
            continue
        if _resolve_proof_line_index(lines, line_no) is None:
            return True
    return False


def _mark_thy_disk_changed(
    server_pool: Optional[IsabelleServerSessionPool],
) -> None:
    """标记 .thy 已在磁盘修改，下次 use_theories 前将重启 session。"""
    if server_pool is not None and server_pool.is_active:
        if not (
            server_pool._thy_loaded_in_session
            or server_pool._thy_seen_in_session
        ):
            return
        server_pool.mark_thy_stale()


def _run_repair_refresh_verify(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    round_idx: int,
    logs: List[str],
    server_pool: Optional[IsabelleServerSessionPool],
) -> Tuple[int, str]:
    """回填后 re-verify，获取最新报错行（避免仅依赖初次 verify 的冻结列表）。"""
    prepare_session_for_repair_refresh_verify(server_pool)
    code, out = _run_use_thy(
        thy_path,
        config,
        tag=f"repair_verify_{round_idx}",
        server_pool=server_pool,
    )
    logs.append(f"[repair_verify_{round_idx}] return_code={code}\n{out}")
    return code, out


def _repair_stuck_verify_with_sledgehammer(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    verify_output: str,
    logs: List[str],
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> Tuple[int, str]:
    """
    verify wall-clock 超时（jEdit 紫色卡住）后：启发式选取证明行 → sledgehammer → 回填。
    """
    repairs = 0
    last_out = verify_output
    max_rounds = config.max_failure_repair_rounds
    repair_started = time.monotonic()
    skipped_indices: Set[int] = set()
    attempt_by_index: dict[int, List[str]] = {}

    print(
        "[stuck-repair] 验证超时，按启发式选取可能卡住的证明步并 sledgehammer ...",
        flush=True,
    )
    _on_verify_wall_timeout(server_pool, "stuck-repair-prep")

    for round_idx in range(1, max_rounds + 1):
        if time.monotonic() - repair_started > config.repair_budget_sec:
            print(
                f"[stuck-repair {round_idx}] 定向修复预算 "
                f"{config.repair_budget_sec}s 已用尽，交回外层 LLM 报错修复",
                flush=True,
            )
            return repairs, last_out
        lines = thy_path.read_text(encoding="utf-8").splitlines()
        target_idx = _pick_stuck_repair_target(lines, skipped_indices)
        if target_idx is None:
            print(
                f"[stuck-repair {round_idx}] 无更多可替换证明行，停止",
                flush=True,
            )
            return repairs, last_out

        target_line_no = target_idx + 1
        if _is_sledgehammer_line(lines[target_idx]):
            if re.fullmatch(r"\s*sledgehammer\s*", lines[target_idx]):
                indent = re.match(r"^\s*", lines[target_idx]).group(0)
                lines[target_idx] = f"{indent}{_sledgehammer_command(config)}"
                thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                _mark_thy_disk_changed(server_pool)
            change_log = (
                f"行 {target_idx + 1} 已有 sledgehammer 占位，直接运行 hammer 回填"
            )
        else:
            target_idx, change_log = _prepare_failed_step_for_sledgehammer(
                lines, target_idx, hammer_cmd=_sledgehammer_command(config)
            )
            thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            ensure_thy_single_closure(thy_path, server_pool=server_pool)
            _mark_thy_disk_changed(server_pool)
        print(
            f"[stuck-repair {round_idx}/{max_rounds}] 疑似卡住行 {target_line_no}："
            f"{change_log}",
            flush=True,
        )

        _ensure_holes_are_closed(thy_path, server_pool=server_pool)
        refreshed_idx = _find_single_sledgehammer_line(
            thy_path, near_idx=target_idx
        )
        if refreshed_idx is not None:
            if refreshed_idx != target_idx:
                print(
                    f"[repair {round_idx}] 清洗后行号位移，"
                    f"hammer 行 {target_idx + 1} → {refreshed_idx + 1}",
                    flush=True,
                )
            target_idx = refreshed_idx
            target_line_no = target_idx + 1
        prepare_session_for_repair_sledgehammer(server_pool)

        code, out = _run_use_thy(
            thy_path,
            config,
            tag=f"stuck_repair_round_{round_idx}",
            server_pool=server_pool,
        )
        logs.append(f"[stuck_repair={round_idx}] return_code={code}\n{out}")
        last_out = out

        if _is_stuck_verify_output(out):
            print(
                f"[stuck-repair {round_idx}] sledgehammer 等待 Try this 超时"
                f"（{config.timeout}s），尝试回退方法 ...",
                flush=True,
            )
            ok, fb_out = _try_fallback_methods_for_sledgehammer(
                thy_path,
                target_idx,
                config,
                logs,
                server_pool,
                round_idx=round_idx,
                deadline=repair_started + config.repair_budget_sec,
            )
            last_out = fb_out if fb_out else out
            if ok:
                repairs += 1
                if _verification_passed(0, fb_out or ""):
                    return repairs, fb_out
                continue
            return repairs, last_out

        suggestions = _extract_try_this_suggestions(out, line_no=target_line_no)
        if not suggestions:
            suggestions = _extract_try_this_suggestions(out)
        applied: Optional[str] = None
        if suggestions:
            applied = _pick_closing_suggestion(suggestions) or suggestions[0].strip()
            if _replace_first_sledgehammer_at_line(
                thy_path, target_idx, applied, server_pool=server_pool
            ):
                _mark_thy_disk_changed(server_pool)
                repairs += 1
                print(
                    f"[stuck-repair {round_idx}] 已回填 → {applied[:160]}",
                    flush=True,
                )
        else:
            print(
                f"[stuck-repair {round_idx}] 行 {target_idx + 1} 无 Try this"
                f"（{config.timeout}s 内），尝试回退方法 ...",
                flush=True,
            )
            ok, fb_out = _try_fallback_methods_for_sledgehammer(
                thy_path,
                target_idx,
                config,
                logs,
                server_pool,
                round_idx=round_idx,
                deadline=repair_started + config.repair_budget_sec,
            )
            last_out = fb_out if fb_out else out
            if ok:
                repairs += 1
                if _verification_passed(0, fb_out or ""):
                    return repairs, fb_out
                continue
            return repairs, last_out

        history = attempt_by_index.setdefault(target_idx, [])
        norm = _normalize_tactic(applied)
        if norm in history:
            print(
                f"[stuck-repair {round_idx}] 行 {target_idx + 1} 重复建议，"
                f"停止 stuck-repair",
                flush=True,
            )
            return repairs, last_out
        history.append(norm)

        verify_code, verify_out = _run_repair_refresh_verify(
            thy_path, config, round_idx, logs, server_pool
        )
        last_out = verify_out
        if _verification_passed(verify_code, verify_out):
            return repairs, verify_out
        if _is_stuck_verify_output(verify_out):
            skipped_indices.add(target_idx)

    return repairs, last_out


def _collect_available_lemma_names(thy_path: Path) -> List[str]:
    """从 sketch 的 imports 引用的 .thy 文件中提取 lemma 名（排除 defs 等纯定义文件）。"""
    try:
        text = thy_path.read_text(encoding="utf-8")
    except Exception:
        return []
    m = re.search(r"^\s*imports\s+(.+)$", text, re.IGNORECASE | re.MULTILINE)
    if not m:
        return []
    sketch_dir = thy_path.parent
    names: List[str] = []
    for tok in m.group(1).split():
        tok = tok.strip().strip('"')
        if not tok or tok == "Main":
            continue
        # 跳过纯函数定义文件（defs），其内无 lemma
        base = tok.rstrip("/").split("/")[-1]
        if base == "defs" or base.endswith("_defs"):
            continue
        cand = (sketch_dir / (tok + ".thy"))
        if not cand.is_file():
            cand = (sketch_dir / tok)
            if cand.suffix != ".thy":
                cand = cand.with_suffix(".thy")
        if not cand.is_file():
            continue
        try:
            dep_text = cand.read_text(encoding="utf-8")
        except Exception:
            continue
        for lm in re.finditer(
            r"^\s*lemma\s+([A-Za-z0-9_']+)", dep_text, re.MULTILINE
        ):
            names.append(lm.group(1))
    seen: set[str] = set()
    out: List[str] = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def _set_thy_line(
    thy_path: Path, idx: int, content: str, server_pool=None
) -> None:
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    if idx < 0 or idx >= len(lines):
        return
    lines[idx] = content
    thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    ensure_thy_single_closure(thy_path, server_pool=server_pool)


def _try_fallback_methods_for_sledgehammer(
    thy_path: Path,
    target_idx: int,
    config: IsabelleRunnerConfig,
    logs: List[str],
    server_pool: Optional[IsabelleServerSessionPool] = None,
    *,
    round_idx: int,
    deadline: Optional[float] = None,
    preferred_candidates: Optional[Sequence[str]] = None,
    target_error_signature: Optional[str] = None,
) -> Tuple[bool, str]:
    """
    sledgehammer 未给出 Try this 建议时的回退：依次尝试一组标准/引理感知证明方法，
    或优先逐条验证本次 hammer 实际返回的 Try this 建议（preferred_candidates）。
    通过实际 use_thy 验证哪个能闭合当前 sledgehammer 步骤。

    判定逻辑（关键修复）：
    - 若候选使整体验证通过 → 完全成功，保留该方法。
    - 若候选使报错**离开当前行**（错误行号 ≠ target）→ 该步已闭合，保留该方法，
      让修复循环继续处理下一个错误（避免多错误时全部候选被丢弃）。
    - 若报错仍在当前行 → 该候选无效，尝试下一个。
    - 全部候选均无法闭合该步 → 用 ``sorry`` 替代 sledgehammer（避免后续 verify
      在 sledgehammer 上反复卡死 60s），返回 False 触发 E4 草图修复。
    """
    # use_thy 内部还会再跑一次 ensure_thy_single_closure，行号可能再次位移；
    # 这里按“文件中唯一的 sledgehammer 行”重新定位，避免建议写到别的行后静默失败。
    relocated = _find_single_sledgehammer_line(thy_path, near_idx=target_idx)
    if relocated is not None:
        target_idx = relocated
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    if target_idx < 0 or target_idx >= len(lines):
        return False, ""
    original_line = lines[target_idx]
    if not re.search(r"\bsledgehammer(?:\s*\[[^\]]*\])?\s*$", original_line):
        return False, ""

    target_line_no = target_idx + 1
    lemma_names = _collect_available_lemma_names(thy_path)
    lemmas_joined = " ".join(lemma_names)

    # 先试“单条可用引理 + simp/blast”，再试通用战术。
    # 旧实现把通用战术放前面并在 6 个处截断，导致引理感知候选永远轮不到，
    # typedef 投影（如 alist_of）这类目标只能反复失败。
    candidates: List[str] = []
    if preferred_candidates:
        for cand in preferred_candidates:
            norm = _normalize_tactic(cand)
            if norm and _is_acceptable_tactic(norm) and norm not in candidates:
                candidates.append(norm)
    context = "\n".join(lines[max(0, target_idx - 6) : target_idx + 1])
    # typedef 的 morphism/inverse 事实不在 lemma_names 里（defs.thy 被跳过），
    # 这里按上下文直接补上旧项目用过的兜底候选。
    if "Abs_bstack_inverse" in context:
        candidates.append("by (simp add: Abs_bstack_inverse)")
    if "Abs_pq_inverse" in context:
        candidates.append("by (simp add: Abs_pq_inverse)")
    if "alist_of" in context:
        candidates.append("using alist_of by simp")
        candidates.append("by (metis alist_of mem_Collect_eq)")
    for name in lemma_names[:6]:
        candidates.extend(
            [
                f"using {name} by simp",
                f"using {name} by blast",
                f"by (metis {name})",
            ]
        )
    if lemma_names:
        candidates.extend(
            [
                f"using {lemmas_joined} by simp",
                f"using {lemmas_joined} by blast",
                f"by (metis {lemmas_joined})",
                f"by (meson {lemmas_joined})",
            ]
        )
    candidates.extend(
        [
            "by simp",
            "by blast",
            "by auto",
            "by arith",
            "by (smt arith)",
            "by (smt)",
        ]
    )

    max_candidates = max(1, int(getattr(config, "max_fallback_candidates", 6)))
    candidates = candidates[:max_candidates]
    fallback_timeout = max(
        10,
        min(
            int(getattr(config, "fallback_candidate_timeout_sec", 20)),
            getattr(config, "timeout", 60),
        ),
    )
    last_out = ""
    for cand_idx, cand in enumerate(candidates):
        if deadline is not None and time.monotonic() > deadline:
            print(
                f"[repair {round_idx}] 回退候选预算已用尽，停止机械尝试并交回 LLM 修复",
                flush=True,
            )
            _set_thy_line(thy_path, target_idx, original_line, server_pool=server_pool)
            return False, last_out
        if not _replace_first_sledgehammer_at_line(
            thy_path, target_idx, cand, server_pool=server_pool
        ):
            _set_thy_line(thy_path, target_idx, original_line, server_pool=server_pool)
            return False, last_out
        # 候选是普通证明方法（不含 hammer），靠 .thy 指纹变化触发 purge 即可；
        # 每条候选都重启 session 会为一次回填多付 15s 以上。
        _mark_thy_disk_changed(server_pool)
        code, out = _run_use_thy(
            thy_path,
            config,
            tag=f"repair_round_{round_idx}_fallback",
            server_pool=server_pool,
            watchdog_timeout=fallback_timeout,
        )
        logs.append(
            f"[fallback={round_idx}] candidate={cand[:80]!r} return_code={code}\n{out}"
        )
        last_out = out
        if _verification_passed(code, out):
            _mark_thy_disk_changed(server_pool)
            print(
                f"[repair {round_idx}] 候选方法成功 → {cand[:120]}",
                flush=True,
            )
            return True, out
        # 报错是否已离开当前行？若离开则该步已闭合，保留候选，让修复循环处理下一个错误
        error_positions = _extract_error_positions(out)
        if target_error_signature and error_positions:
            signatures = {_goal_signature(msg) for _ln, msg in error_positions}
            if target_error_signature not in signatures:
                _mark_thy_disk_changed(server_pool)
                print(
                    f"[repair {round_idx}] 候选方法闭合该步（原目标已消失）→ {cand[:120]}",
                    flush=True,
                )
                return True, out
            _set_thy_line(thy_path, target_idx, original_line, server_pool=server_pool)
            continue
        error_at_target = any(
            ln == target_line_no for ln, _ in error_positions
        )
        if not error_at_target and error_positions:
            _mark_thy_disk_changed(server_pool)
            print(
                f"[repair {round_idx}] 回退方法闭合该步（错误已移至他行）→ {cand[:120]}",
                flush=True,
            )
            return True, out
        # 报错仍在当前行：恢复 sledgehammer 占位以尝试下一个候选
        _set_thy_line(thy_path, target_idx, original_line, server_pool=server_pool)
    # 全部候选均无法闭合该步：用 sorry 替代 sledgehammer 避免后续反复卡死
    # （quick_and_dirty 下 sorry 可通过 E 阶段；若位于主定理，F4 final 验证会失败，
    #  进而触发 E4 草图修复由 LLM 重新生成证明。）
    _set_thy_line(thy_path, target_idx, "sorry", server_pool=server_pool)
    _mark_thy_disk_changed(server_pool)
    print(
        f"[repair {round_idx}] sledgehammer 无建议且回退方法均无法闭合该步，"
        f"临时替换为 sorry 以避免卡死",
        flush=True,
    )
    return False, last_out


def _repair_failed_steps_with_sledgehammer(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    verify_output: str,
    logs: List[str],
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> Tuple[int, str]:
    """
    验证失败后：按 Isabelle 报错行号将失败证明步替换为 sledgehammer，再尝试回填。
    每轮只修一处；若上一行是 using，则删除 using 并与当前证明行合并为一行 sledgehammer。
    成功回填后会 re-verify 刷新报错行；冻结列表无法映射时也会 re-verify 一次再试。
    由调用方在 repair 结束后统一执行 repair_final_verify。
    """
    repairs = 0
    last_out = verify_output
    verify_error_output = verify_output
    max_rounds = config.max_failure_repair_rounds
    repair_started = time.monotonic()
    skipped_indices: Set[int] = set()
    skipped_line_numbers: Set[int] = set()
    attempt_by_index: dict[int, List[str]] = {}

    for round_idx in range(1, max_rounds + 1):
        if time.monotonic() - repair_started > config.repair_budget_sec:
            print(
                f"[repair {round_idx}] 定向修复预算 {config.repair_budget_sec}s 已用尽，"
                f"交回外层 LLM 报错修复",
                flush=True,
            )
            return repairs, last_out
        retried_after_refresh = False
        while True:
            positions = _extract_error_positions(verify_error_output)
            repairable = [
                (ln, msg) for ln, msg in positions if _is_repairable_proof_error(msg)
            ]
            if not repairable:
                print(
                    f"[repair {round_idx}] 未发现可修复的证明步骤错误，停止定向修复",
                    flush=True,
                )
                return repairs, last_out

            lines = thy_path.read_text(encoding="utf-8").splitlines()
            target_line_no, target_idx = _pick_repair_target(
                lines, repairable, skipped_indices, skipped_line_numbers
            )

            if target_idx is not None:
                break

            if retried_after_refresh or not _has_unmapped_repairable_errors(
                lines, repairable, skipped_line_numbers
            ):
                print(
                    f"[repair {round_idx}] 报错行无法映射到可替换的证明命令行，停止定向修复",
                    flush=True,
                )
                return repairs, last_out

            print(
                "[repair] 冻结报错行均无法映射，重新 verify 以刷新报错行 ...",
                flush=True,
            )
            verify_code, verify_out = _run_repair_refresh_verify(
                thy_path, config, round_idx, logs, server_pool
            )
            last_out = verify_out
            if _verification_passed(verify_code, verify_out):
                return repairs, verify_out
            verify_error_output = verify_out
            retried_after_refresh = True

        if _is_sledgehammer_line(lines[target_idx]):
            if re.fullmatch(r"\s*sledgehammer\s*", lines[target_idx]):
                indent = re.match(r"^\s*", lines[target_idx]).group(0)
                lines[target_idx] = f"{indent}{_sledgehammer_command(config)}"
                thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                _mark_thy_disk_changed(server_pool)
            change_log = (
                f"行 {target_idx + 1} 已有 sledgehammer 占位，直接运行 hammer 回填"
            )
        else:
            target_idx, change_log = _prepare_failed_step_for_sledgehammer(
                lines, target_idx, hammer_cmd=_sledgehammer_command(config)
            )
            thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            ensure_thy_single_closure(thy_path, server_pool=server_pool)
            _mark_thy_disk_changed(server_pool)
        print(
            f"[repair {round_idx}/{max_rounds}] 报错行 {target_line_no}：{change_log}",
            flush=True,
        )

        target_error_signature = _error_signature_at_line(
            verify_error_output, target_line_no
        )
        _ensure_holes_are_closed(thy_path, server_pool=server_pool)
        # 补 sorry / 规范化 end 闭包会增删空行，_prepare 返回的下标会失效；
        # 回填前必须按“文件中唯一的 sledgehammer 行”重定位，否则建议写到别的行上。
        refreshed_idx = _find_single_sledgehammer_line(
            thy_path, near_idx=target_idx
        )
        if refreshed_idx is not None:
            if refreshed_idx != target_idx:
                print(
                    f"[repair {round_idx}] 清洗后行号位移，"
                    f"hammer 行 {target_idx + 1} → {refreshed_idx + 1}",
                    flush=True,
                )
            target_idx = refreshed_idx
        prepare_session_for_repair_sledgehammer(server_pool)

        code, out = _run_use_thy(
            thy_path, config, tag=f"repair_round_{round_idx}", server_pool=server_pool
        )
        logs.append(f"[repair={round_idx}] return_code={code}\n{out}")
        last_out = out

        if _is_stuck_verify_output(out):
            print(
                f"[repair {round_idx}] sledgehammer 等待 Try this 超时"
                f"（{config.timeout}s），尝试回退方法 ...",
                flush=True,
            )
            ok, fb_out = _try_fallback_methods_for_sledgehammer(
                thy_path,
                target_idx,
                config,
                logs,
                server_pool,
                round_idx=round_idx,
                deadline=repair_started + config.repair_budget_sec,
                target_error_signature=target_error_signature,
            )
            if ok:
                repairs += 1
                last_out = fb_out
                verify_error_output = fb_out
                if target_line_no is not None:
                    skipped_line_numbers.add(target_line_no)
                if _verification_passed(0, fb_out):
                    return repairs, fb_out
                continue
            return repairs, last_out

        suggestions = _extract_try_this_suggestions(out, line_no=target_line_no)
        if not suggestions:
            suggestions = _extract_try_this_suggestions(out)
        if suggestions:
            # 旧版只取第一条建议；若第一条（如 z3 的 fastforce）不闭合目标，
            # 会反复回填同一条并最终退化成 sorry。这里像旧项目一样逐条真验，
            # 直到某条建议使验证通过或报错离开当前行。
            print(
                f"[repair {round_idx}] 获得 {len(suggestions)} 条 Try this，逐条验证 ...",
                flush=True,
            )
            ok, fb_out = _try_fallback_methods_for_sledgehammer(
                thy_path,
                target_idx,
                config,
                logs,
                server_pool,
                round_idx=round_idx,
                deadline=repair_started + config.repair_budget_sec,
                preferred_candidates=suggestions[:3],
                target_error_signature=target_error_signature,
            )
            if ok:
                repairs += 1
                last_out = fb_out
                verify_error_output = fb_out
                if target_line_no is not None:
                    skipped_line_numbers.add(target_line_no)
                if _verification_passed(0, fb_out):
                    return repairs, fb_out
                continue
            return repairs, last_out

        print(
            f"[repair {round_idx}] 未获得 Try this 建议"
            f"（{config.timeout}s 内），尝试回退方法 ...",
            flush=True,
        )
        ok, fb_out = _try_fallback_methods_for_sledgehammer(
            thy_path,
            target_idx,
            config,
            logs,
            server_pool,
            round_idx=round_idx,
            deadline=repair_started + config.repair_budget_sec,
            target_error_signature=target_error_signature,
        )
        if ok:
            repairs += 1
            last_out = fb_out
            verify_error_output = fb_out
            if target_line_no is not None:
                skipped_line_numbers.add(target_line_no)
            if _verification_passed(0, fb_out):
                return repairs, fb_out
            continue
        return repairs, last_out

    return repairs, last_out


def format_isabelle_error_for_prompt(
    verify_output: str,
    *,
    max_chars: int = 12000,
) -> str:
    """
    将 Isabelle 验证输出整理为可放入 LLM 修复提示词的错误摘要。
    优先展示根因错误，省略 missing theory context 等连锁语法报错。
    """
    out = (verify_output or "").strip()
    if not out:
        return "(未捕获到 Isabelle 错误输出)"

    positions = _extract_error_positions(out)
    summarized, suppressed = _summarize_error_positions(positions)
    parts: List[str] = []
    if summarized:
        parts.append("## 主要错误（已去重）")
        for line_no, msg in summarized[:15]:
            parts.append(f"- line {line_no}: {msg}")
        if suppressed > 0:
            parts.append(
                f"- （已省略 {suppressed} 条由同一根因引起的连锁语法错误，"
                f"如 missing theory context）"
            )
        parts.append("")

    parts.append("## Full verification output")
    body = out
    if len(body) > max_chars:
        body = body[:max_chars] + "\n... (verification output truncated)"
    parts.append(body)
    return "\n".join(parts)


def _verification_passed(return_code: int, output: str) -> bool:
    if return_code != 0:
        return False
    if _is_transient_isabelle_server_error(output):
        return False
    fatal_markers = (
        "Failed to finish proof",
        "Failed to apply initial proof method",
        "Undefined case",
        "Illegal application of proof command",
        "Undefined fact",
    )
    return not any(m in (output or "") for m in fatal_markers)


def _replace_sledgehammer_lines(
    thy_path: Path,
    output: str,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> int:
    """按 Isabelle 报错行号将 sledgehammer 占位符替换为 Try this 建议。"""
    by_line = _extract_try_this_by_line(output)
    if not by_line:
        return 0
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    replaced = 0
    fallback = by_line.get(0, [])
    fallback_idx = 0
    drop_sorry: Set[int] = set()
    for i, line in enumerate(lines):
        if not re.search(r"\bsledgehammer(?:\s*\[[^\]]*\])?\s*$", line):
            continue
        line_no = i + 1
        candidates = by_line.get(line_no, [])
        if candidates:
            suggestion = _pick_closing_suggestion(candidates) or candidates[0].strip()
        elif fallback_idx < len(fallback):
            suggestion = fallback[fallback_idx].strip()
            fallback_idx += 1
        else:
            continue
        m = re.match(r"^(.*?)(?:\s*)sledgehammer(?:\s*\[[^\]]*\])?\s*$", line)
        if not m:
            continue
        prefix = (m.group(1) or "").rstrip()
        if prefix:
            lines[i] = f"{prefix} {suggestion}"
        else:
            indent = re.match(r"^\s*", line).group(0)
            lines[i] = f"{indent}{suggestion}"
        if _suggestion_closes_goal(suggestion):
            sorry_idx = _find_hole_closing_sorry(lines, i)
            if sorry_idx is not None and sorry_idx not in drop_sorry:
                drop_sorry.add(sorry_idx)
        replaced += 1
    if drop_sorry:
        lines = [ln for j, ln in enumerate(lines) if j not in drop_sorry]
    if replaced > 0:
        thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        ensure_thy_single_closure(thy_path, server_pool=server_pool)
        _mark_thy_disk_changed(server_pool)
    return replaced


def _sanitize_companion_theories(
    thy_path: Path,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> bool:
    """验证 sketch 前同步清洗同目录下 imports 的 companion .thy。"""
    if not thy_path.is_file():
        return False
    text = thy_path.read_text(encoding="utf-8")
    changed = False
    skip = {"Main", "HOL", "Complex", "Real"}
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.lower().startswith("imports "):
            continue
        for token in stripped[len("imports"):].split():
            name = token.strip().strip('"')
            if not name or name in skip or "." in name:
                continue
            companion = thy_path.parent / f"{name}.thy"
            if companion.is_file() and _sanitize_theory_before_verify(
                companion, server_pool=server_pool
            ):
                changed = True
    if changed:
        _mark_thy_disk_changed(server_pool)
    return changed


def _prepare_thy_for_verify(
    thy_path: Path,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> bool:
    from .lemma_dedup import truncate_theory_to_first_closure

    raw = thy_path.read_text(encoding="utf-8")
    trimmed = truncate_theory_to_first_closure(raw)
    if trimmed != raw:
        thy_path.write_text(trimmed, encoding="utf-8")
        _mark_thy_disk_changed(server_pool)
    companion_changed = _sanitize_companion_theories(thy_path, server_pool=server_pool)
    sanitized = _sanitize_theory_before_verify(thy_path, server_pool=server_pool)
    if _ensure_holes_are_closed(thy_path, server_pool=server_pool):
        sanitized = True
    if sanitized or companion_changed:
        _mark_thy_disk_changed(server_pool)
    return sanitized or companion_changed


def _run_verify_and_repair_with_pool(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: IsabelleServerSessionPool,
    *,
    sanitized: bool,
    total_replaced: int = 0,
    logs: Optional[List[str]] = None,
    verify_tag: str = "verify",
) -> dict:
    logs = logs if logs is not None else []
    print(
        f"[{verify_tag}] 正在验证 {thy_path.name}（watchdog {config.verify_timeout}s，"
        f"wall-clock {config.verify_wall_timeout_sec}s）...",
        flush=True,
    )
    verify_code, verify_out = _run_use_thy(
        thy_path, config, tag=verify_tag, server_pool=server_pool
    )
    logs.append(f"[{verify_tag}] return_code={verify_code}\n{verify_out}")
    stuck = _is_stuck_verify_output(verify_out)
    success = _verification_passed(verify_code, verify_out) and not stuck
    failure_repairs = 0

    if not success and _is_transient_isabelle_server_error(verify_out):
        print(
            "[repair] 验证结果是 server 瞬态故障（非证明失败），"
            "重启 server 后重试 ...",
            flush=True,
        )
        if server_pool.is_active:
            server_pool.restart_server()
        verify_code, verify_out = _run_use_thy(
            thy_path,
            config,
            tag=f"{verify_tag}_infra_retry",
            server_pool=server_pool,
        )
        logs.append(
            f"[{verify_tag}_infra_retry] return_code={verify_code}\n{verify_out}"
        )
        stuck = _is_stuck_verify_output(verify_out)
        success = _verification_passed(verify_code, verify_out) and not stuck

    if not success and config.repair_failed_steps:
        if stuck:
            if _stuck_verify_is_likely_load_stall(verify_out):
                print(
                    "[repair] STUCK_VERIFY 且无证明报错，跳过 stuck-repair，"
                    "重启 session 后重试 verify ...",
                    flush=True,
                )
                prepare_session_for_repair_final_verify(server_pool)
                verify_code, verify_out = _run_use_thy(
                    thy_path,
                    config,
                    tag="verify_load_stall_retry",
                    server_pool=server_pool,
                )
                logs.append(
                    f"[verify_load_stall_retry] return_code={verify_code}\n{verify_out}"
                )
                success = _verification_passed(verify_code, verify_out) and not (
                    _is_stuck_verify_output(verify_out)
                )
            else:
                print(
                    "[repair] 验证 wall-clock 超时（疑似 jEdit 紫色卡住），"
                    "启动 stuck-repair ...",
                    flush=True,
                )
                failure_repairs, verify_out = _repair_stuck_verify_with_sledgehammer(
                    thy_path, config, verify_out, logs, server_pool=server_pool
                )
                prepare_session_for_repair_final_verify(server_pool)
                verify_code, verify_out = _run_use_thy(
                    thy_path, config, tag="repair_final_verify", server_pool=server_pool
                )
                logs.append(
                    f"[repair_final_verify] return_code={verify_code}\n{verify_out}"
                )
                success = _verification_passed(verify_code, verify_out)
        else:
            print(
                "[repair] 验证未通过，开始对失败证明步做定向 sledgehammer 修复 ...",
                flush=True,
            )
            failure_repairs, verify_out = _repair_failed_steps_with_sledgehammer(
                thy_path, config, verify_out, logs, server_pool=server_pool
            )
            prepare_session_for_repair_final_verify(server_pool)
            verify_code, verify_out = _run_use_thy(
                thy_path, config, tag="repair_final_verify", server_pool=server_pool
            )
            logs.append(
                f"[repair_final_verify] return_code={verify_code}\n{verify_out}"
            )
            success = _verification_passed(verify_code, verify_out)

    # 修复后若 .thy 正文仍含 sorry（主定理证明步），视为未真正验证通过：
    # quick_and_dirty 下 Isabelle 会接受 sorry，但主定理的 sorry 意味着证明未完成，
    # 应触发 E4 草图修复由 LLM 重新生成。仅对草图文件（_sketch.thy）启用此检查，
    # 避免误伤引理证明阶段（F2 中 unproven 引理含 sorry 是正常的）。
    if success and "_sketch" in thy_path.stem:
        try:
            content = thy_path.read_text(encoding="utf-8")
        except Exception:
            content = ""
        if re.search(r"^\s*sorry\s*$", content, re.MULTILINE) or re.search(
            r"\bsorry\b\s*$", content, re.MULTILINE
        ):
            print(
                f"[verify] {thy_path.name} 仍含 sorry（主定理证明未完成），"
                f"标记为未通过以触发草图修复",
                flush=True,
            )
            success = False

    return {
        "thy_file": str(thy_path),
        "sanitized_before_verify": sanitized,
        "success": success,
        "replaced_sledgehammer_count": total_replaced,
        "failure_repair_count": failure_repairs,
        "verify_return_code": verify_code,
        "verify_output": verify_out,
        "needs_llm_repair": not success,
        "round_logs": logs,
    }


def verify_thy_with_repair(
    thy_file: str,
    config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> dict:
    """仅对 .thy 做语法清洗与 Isabelle 验证（含可选失败步 repair），不做 sledgehammer 回填。"""
    thy_path = Path(thy_file)
    if not thy_path.exists():
        raise FileNotFoundError(f".thy 文件不存在: {thy_path}")
    if server_pool is not None and server_pool.is_active:
        return _verify_thy_with_repair_with_pool(thy_path, config, server_pool)
    with IsabelleServerSessionPool(config) as pool:
        return _verify_thy_with_repair_with_pool(thy_path, config, pool)


def _verify_thy_with_repair_with_pool(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: IsabelleServerSessionPool,
) -> dict:
    sanitized = _prepare_thy_for_verify(thy_path, server_pool)
    return _run_verify_and_repair_with_pool(
        thy_path, config, server_pool, sanitized=sanitized, verify_tag="verify"
    )


def process_sledgehammer_and_verify(
    thy_file: str,
    config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> dict:
    """
    完整 .thy 后处理：
    1) 若含 sledgehammer 占位符，先多轮 hammer 回填
    2) 再验证；失败则按报错行定向 sledgehammer 修复
    """
    thy_path = Path(thy_file)
    if not thy_path.exists():
        raise FileNotFoundError(f".thy 文件不存在: {thy_path}")
    if server_pool is not None and server_pool.is_active:
        return _process_sledgehammer_entry(thy_path, config, server_pool)
    with IsabelleServerSessionPool(config) as pool:
        return _process_sledgehammer_entry(thy_path, config, pool)


def _process_sledgehammer_entry(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: IsabelleServerSessionPool,
) -> dict:
    if _has_sledgehammer_lines(thy_path):
        print(
            f"[sledgehammer] {thy_path.name} 含 sledgehammer 占位符，先执行回填轮次 ...",
            flush=True,
        )
        return _process_sledgehammer_and_verify_with_pool(
            thy_path, config, server_pool
        )
    return _verify_thy_with_repair_with_pool(thy_path, config, server_pool)


def _convert_holes_to_sorry(thy_path: Path) -> List[int]:
    """将每个 sledgehammer 洞收敛为单行 sorry，返回 sorry 行下标（从下往上）。

    从下往上处理可保证已处理的行不影响上方行号。
    """
    try:
        lines = thy_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []

    indices: List[int] = []
    i = 0
    while i < len(lines):
        if not _is_sledgehammer_line(lines[i]) or lines[i].lstrip().startswith("(*"):
            i += 1
            continue
        sorry_idx = _find_hole_closing_sorry(lines, i)
        if sorry_idx is None:
            indent = re.match(r"^\s*", lines[i]).group(0)
            lines[i] = f"{indent}sorry"
            indices.append(i)
            i += 1
            continue
        del lines[i]
        indices.append(sorry_idx - 1)
        i = sorry_idx
    thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return sorted(indices, reverse=True)


def _backfill_holes_sequentially(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool],
    logs: List[str],
) -> int:
    """旧版行为：每次只让一个洞存在 sledgehammer，其余保持 sorry。

    单个目标超时只影响该目标，不会因一个慢目标丢掉其他洞的 Try this。
    """
    hole_indices = _convert_holes_to_sorry(thy_path)
    if not hole_indices:
        return 0
    total_holes = len(hole_indices)
    print(
        f"[sledgehammer] 逐洞回填：共 {total_holes} 个洞，"
        f"每个洞 wall-clock {max(90, config.sledgehammer_hole_timeout_sec + 90)}s",
        flush=True,
    )
    replaced = 0
    started = time.monotonic()
    done = 0
    for idx in hole_indices:
        if time.monotonic() - started > config.repair_budget_sec + config.sledgehammer_round_max_wall_sec:
            print("[sledgehammer] 总预算已用尽，停止回填", flush=True)
            break
        lines = thy_path.read_text(encoding="utf-8").splitlines()
        if idx < 0 or idx >= len(lines) or not _is_sorry_closing_line(lines[idx]):
            continue
        done += 1
        indent = re.match(r"^\s*", lines[idx]).group(0)
        lines.insert(idx, f"{indent}{_sledgehammer_command(config)}")
        thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        _mark_thy_disk_changed(server_pool)
        print(
            f"[sledgehammer] 回填 {done}/{total_holes}（行 {idx + 1}）...",
            flush=True,
        )
        code, out = _run_use_thy(
            thy_path,
            config,
            tag="sledgehammer_hole",
            server_pool=server_pool,
            watchdog_timeout=config.sledgehammer_hole_timeout_sec + 30,
            wall_timeout=max(90, config.sledgehammer_hole_timeout_sec + 90),
        )
        logs.append(f"[hole={done} line={idx + 1}] return_code={code}\n{out}")
        suggestions = _extract_try_this_suggestions(out, line_no=idx + 1)
        if not suggestions:
            suggestions = _extract_try_this_suggestions(out)
        relocated = _find_single_sledgehammer_line(thy_path, near_idx=idx)
        if relocated is not None:
            idx = relocated
        if not suggestions:
            lines = thy_path.read_text(encoding="utf-8").splitlines()
            if idx < len(lines) and _is_sledgehammer_line(lines[idx]):
                del lines[idx]
                thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                _mark_thy_disk_changed(server_pool)
            print(f"[sledgehammer] 行 {idx + 1} 未获得 Try this", flush=True)
            continue
        applied = _pick_closing_suggestion(suggestions) or suggestions[0].strip()
        lines = thy_path.read_text(encoding="utf-8").splitlines()
        if idx >= len(lines) or not _is_sledgehammer_line(lines[idx]):
            continue
        lines[idx] = f"{indent}{applied}"
        if _suggestion_closes_goal(applied):
            sorry_idx = _find_hole_closing_sorry(lines, idx)
            if sorry_idx is not None:
                del lines[sorry_idx]
            _drop_stale_sorry_above(lines, idx)
        thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        ensure_thy_single_closure(thy_path, server_pool=server_pool)
        _mark_thy_disk_changed(server_pool)
        replaced += 1
        print(f"[sledgehammer] 行 {idx + 1} 已回填 → {applied[:120]}", flush=True)
    return replaced


def _process_sledgehammer_and_verify_with_pool(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    server_pool: IsabelleServerSessionPool,
) -> dict:
    sanitized = _prepare_thy_for_verify(thy_path, server_pool)

    total_replaced = 0
    logs: List[str] = []
    if config.sledgehammer_backfill_mode == "sequential":
        total_replaced = _backfill_holes_sequentially(
            thy_path, config, server_pool, logs
        )
        return _run_verify_and_repair_with_pool(
            thy_path,
            config,
            server_pool,
            sanitized=sanitized,
            total_replaced=total_replaced,
            logs=logs,
            verify_tag="verify_final",
        )
    max_rounds = config.max_sledgehammer_rounds

    for round_idx in range(1, max_rounds + 1):
        holes = _count_sledgehammer_holes(thy_path)
        round_wall = _sledgehammer_round_wall(config, holes)
        print(
            f"[round {round_idx}/{max_rounds}] 正在运行 Isabelle use_theories ..."
            f"（{holes} 个 sledgehammer 洞，wall-clock {round_wall}s）",
            flush=True,
        )
        code, out = _run_use_thy(
            thy_path,
            config,
            tag=f"sledgehammer_round_{round_idx}",
            server_pool=server_pool,
            wall_timeout=round_wall,
        )
        logs.append(f"[round={round_idx}] return_code={code}\n{out}")
        replaced = _replace_sledgehammer_lines(
            thy_path, out, server_pool=server_pool
        )
        total_replaced += replaced
        print(
            f"[round {round_idx}/{max_rounds}] 本轮替换 sledgehammer: {replaced} 处，累计: {total_replaced}",
            flush=True,
        )
        if replaced == 0:
            print(
                f"[round {round_idx}/{max_rounds}] 无新增替换，提前结束回填轮次",
                flush=True,
            )
            break

    return _run_verify_and_repair_with_pool(
        thy_path,
        config,
        server_pool,
        sanitized=sanitized,
        total_replaced=total_replaced,
        logs=logs,
        verify_tag="verify_final",
    )


def print_thy_verify_result(
    processed: dict,
    *,
    extra_thy_files: Optional[List[str]] = None,
) -> None:
    """打印 .thy 后处理验证结果；失败时附带 Isabelle 报错与相关 .thy 全文。"""
    print("\n" + "=" * 80)
    print("[verify] .thy 后处理验证结果")
    print("=" * 80)
    print(f"theory: {processed['thy_file']}")
    print(
        f"语法清洗: {'已执行并修改' if processed.get('sanitized_before_verify') else '无需修改'}"
    )
    print(f"sledgehammer 替换数: {processed['replaced_sledgehammer_count']}")
    print(f"失败步骤定向修复数: {processed.get('failure_repair_count', 0)}")
    print(f"验证成功: {'是' if processed['success'] else '否'}")
    if not processed["success"]:
        paths_to_print: List[str] = []
        thy_file = processed.get("thy_file")
        if thy_file:
            paths_to_print.append(str(thy_file))
        for extra in extra_thy_files or []:
            if extra and extra not in paths_to_print:
                paths_to_print.append(extra)
        for path_str in paths_to_print:
            thy_path = Path(path_str)
            if thy_path.is_file():
                print(f"\n验证失败的 proof（{thy_path.name}）:")
                print("-" * 80)
                print(thy_path.read_text(encoding="utf-8").rstrip())
                print("-" * 80)
        print("\nIsabelle错误信息:")
        print("-" * 80)
        verify_output = (processed.get("verify_output") or "").strip()
        print(format_isabelle_error_for_prompt(verify_output, max_chars=4000))
        print("-" * 80)
    print("=" * 80 + "\n")

