"""
Isabelle server 进程生命周期：注册活跃 session，在 Ctrl+C / 退出时统一 shutdown，减少 PolyML 孤儿进程。
"""

from __future__ import annotations

import atexit
import signal
import subprocess
import sys
import threading
from typing import Any, Dict, List, Optional, TYPE_CHECKING

if TYPE_CHECKING:
    from .isabelle_sledgehammer import IsabelleServerSessionPool

_lock = threading.RLock()
_handlers_installed = False
_active_pools: List["IsabelleServerSessionPool"] = []
_ephemeral_servers: List[Dict[str, Any]] = []
_tracked_server_pids: set[int] = set()
_kill_orphans_on_shutdown = True


def set_kill_orphans_on_shutdown(enabled: bool) -> None:
    global _kill_orphans_on_shutdown
    _kill_orphans_on_shutdown = enabled


def register_server_pid(pid: Optional[int]) -> None:
    if pid:
        with _lock:
            _tracked_server_pids.add(int(pid))


def _unregister_server_pid(pid: Optional[int]) -> None:
    if pid:
        with _lock:
            _tracked_server_pids.discard(int(pid))


_WINDOWS_ISABELLE_ORPHAN_IMAGES = (
    "poly.exe",
    "bash_process.exe",
    "eprover.exe",
)


def _kill_windows_isabelle_orphans(*, aggressive: bool = True) -> int:
    """
    Isabelle server 关闭后 PolyML / Sledgehammer 外部证明器常成为孤儿进程；
    在 Windows 上按镜像名清理。仅用于 BLProver 退出/中断路径，避免 dev 环境内存被占满。
    """
    if sys.platform != "win32" or not aggressive:
        return 0
    killed = 0
    for image in _WINDOWS_ISABELLE_ORPHAN_IMAGES:
        try:
            proc = subprocess.run(
                ["taskkill", "/F", "/IM", image],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30,
                check=False,
            )
            if proc.returncode == 0:
                killed += 1
        except Exception:
            pass
    with _lock:
        leftover = list(_tracked_server_pids)
    for pid in leftover:
        try:
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(pid)],
                capture_output=True,
                timeout=15,
                check=False,
            )
        except Exception:
            pass
        _unregister_server_pid(pid)
    return killed


def _terminate_subprocess(proc: Any) -> None:
    """终止 server 子进程；Windows 上使用 taskkill /T 杀掉 PolyML 等子进程树。"""
    if proc is None:
        return
    poll = getattr(proc, "poll", None)
    if callable(poll) and poll() is not None:
        return
    pid = getattr(proc, "pid", None)
    if sys.platform == "win32" and pid:
        try:
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(pid)],
                capture_output=True,
                timeout=20,
                check=False,
            )
            wait = getattr(proc, "wait", None)
            if callable(wait):
                try:
                    wait(timeout=5)
                except Exception:
                    pass
            _unregister_server_pid(pid)
            return
        except Exception:
            pass
    terminate = getattr(proc, "terminate", None)
    kill = getattr(proc, "kill", None)
    try:
        if callable(terminate):
            terminate()
        if callable(getattr(proc, "wait", None)):
            proc.wait(timeout=5)
    except Exception:
        if callable(kill):
            try:
                kill()
            except Exception:
                pass
        if sys.platform == "win32" and pid:
            try:
                subprocess.run(
                    ["taskkill", "/F", "/T", "/PID", str(pid)],
                    capture_output=True,
                    timeout=20,
                    check=False,
                )
            except Exception:
                pass


def _close_client_session(client: Any, session_id: Optional[str], proc: Any) -> None:
    if client and session_id:
        try:
            client.session_stop(session_id)
        except Exception:
            pass
    if client:
        try:
            client.shutdown()
        except Exception:
            pass
    _terminate_subprocess(proc)


def install_shutdown_handlers() -> None:
    global _handlers_installed
    if _handlers_installed:
        return
    _handlers_installed = True
    atexit.register(lambda: shutdown_all_isabelle_servers(reason="atexit"))

    def _handler(signum: int, frame: Any) -> None:
        # SIGINT：不在此处 shutdown server，避免 asyncio 仍在 use_theories 时
        # 先杀 server 导致 ConnectionResetError 与 poly 孤儿；清理由 main/finally 完成。
        if signum == signal.SIGINT:
            raise KeyboardInterrupt
        n = shutdown_all_isabelle_servers(reason=f"signal {signum}")
        if n:
            print(
                f"[isabelle_server] 已清理 {n} 个 Isabelle server/session（信号 {signum}）",
                flush=True,
            )

    for sig_name in ("SIGINT", "SIGTERM", "SIGBREAK"):
        sig = getattr(signal, sig_name, None)
        if sig is None:
            continue
        try:
            signal.signal(sig, _handler)
        except (ValueError, OSError):
            pass


def register_pool(pool: "IsabelleServerSessionPool") -> None:
    install_shutdown_handlers()
    with _lock:
        if pool not in _active_pools:
            _active_pools.append(pool)


def unregister_pool(pool: "IsabelleServerSessionPool") -> None:
    with _lock:
        try:
            _active_pools.remove(pool)
        except ValueError:
            pass


def register_ephemeral_server(
    client: Any,
    session_id: Optional[str],
    server_proc: Any = None,
) -> Dict[str, Any]:
    """语法复杂度等单次 server 调用；返回登记项，结束时请 close_ephemeral_server。"""
    install_shutdown_handlers()
    entry = {
        "client": client,
        "session_id": session_id,
        "proc": server_proc,
    }
    with _lock:
        _ephemeral_servers.append(entry)
    register_server_pid(getattr(server_proc, "pid", None))
    return entry


def close_ephemeral_server(entry: Dict[str, Any]) -> None:
    with _lock:
        try:
            _ephemeral_servers.remove(entry)
        except ValueError:
            pass
    _close_client_session(
        entry.get("client"),
        entry.get("session_id"),
        entry.get("proc"),
    )
    if _kill_orphans_on_shutdown:
        _kill_windows_isabelle_orphans(aggressive=True)


def shutdown_all_isabelle_servers(
    *,
    reason: str = "",
    kill_orphans: Optional[bool] = None,
) -> int:
    """关闭所有已登记的 pool 与 ephemeral server。返回清理数量。"""
    with _lock:
        pools = list(_active_pools)
        _active_pools.clear()
        ephemeral = list(_ephemeral_servers)
        _ephemeral_servers.clear()

    closed = 0
    for pool in pools:
        try:
            pool.close(kill_orphans=False)
            closed += 1
        except Exception:
            pass

    for entry in ephemeral:
        try:
            _close_client_session(
                entry.get("client"),
                entry.get("session_id"),
                entry.get("proc"),
            )
            closed += 1
        except Exception:
            pass

    do_orphans = (
        _kill_orphans_on_shutdown if kill_orphans is None else kill_orphans
    )
    orphan_images = _kill_windows_isabelle_orphans(aggressive=do_orphans)
    if orphan_images and reason:
        print(
            f"[isabelle_server] 已清理遗留 Isabelle  worker 进程（{orphan_images} 类镜像）",
            flush=True,
        )
    return closed
