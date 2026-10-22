"""运行阶段看板：控制台精简输出 + 阶段耗时统计 + 终端噪声分流。

设计：
- 控制台默认精简：Isabelle 会话细节、.thy 规范化、等待心跳、artifact 写入、
  LLM 提示词/回复正文等内部细节只写入日志文件，控制台隐藏。
- 日志文件始终全量：内部细节通过 ``emit_detail()`` 写入 tee 的文件侧。
- ``--verbose`` 时全部放开（控制台等同日志文件）。
- 阶段看板：9 个阶段统一编号，进入/退出各一行，结束时打印阶段耗时汇总表。
"""

from __future__ import annotations

import re
import sys
import time
from typing import Dict, List, Optional, Sequence, Tuple

# 阶段定义（顺序即执行顺序）
STAGES: Tuple[Tuple[str, str], ...] = (
    ("construct_lemmas1", "抽取引理（全局策略）"),
    ("informal_proof", "生成非形式化证明"),
    ("construct_lemmas2", "抽取引理（依赖非形式化证明）"),
    ("formal_sketch", "生成形式化证明草图"),
    ("sketch_verify", "草图验证（Isabelle）"),
    ("failure_repair", "草图/引理修复（验证失败时）"),
    ("lemma_proving", "引理迭代证明"),
    ("finalize", "最终定理验证与归档"),
    ("quality_eval", "引理质量评估与筛选"),
)

STAGE_INDEX: Dict[str, int] = {key: idx for idx, (key, _label) in enumerate(STAGES, 1)}
STAGE_LABEL: Dict[str, str] = {key: label for key, label in STAGES}
TOTAL_STAGES = len(STAGES)

_LINE = "=" * 78
_THIN = "-" * 78

_verbose = False
_file_only_stream = None


def set_verbose(enabled: bool) -> None:
    """设置是否把内部细节也输出到控制台。"""
    global _verbose
    _verbose = bool(enabled)


def is_verbose() -> bool:
    return _verbose


def attach_stream(stream) -> None:
    """注册当前 tee 流，用于「只写日志文件」的输出。"""
    global _file_only_stream
    _file_only_stream = stream


def emit_detail(text: str) -> None:
    """输出内部细节：控制台隐藏（除非 verbose），日志文件始终保留。"""
    body = text if text.endswith("\n") else text + "\n"
    if _verbose or _file_only_stream is None:
        try:
            sys.stdout.write(body)
            sys.stdout.flush()
        except Exception:
            print(text, flush=True)
        return
    writer = getattr(_file_only_stream, "write_file_only", None)
    if writer is None:
        print(text, flush=True)
        return
    try:
        writer(body)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# 控制台噪声过滤
# ---------------------------------------------------------------------------

_INTERNAL_PATTERNS: Sequence[re.Pattern] = (
    re.compile(r"^\[thy\] "),
    re.compile(r"^\[isabelle_server\] "),
    re.compile(r"^\[isabelle\] .*仍在等待"),
    re.compile(r"^\[artifact\] "),
    re.compile(r"^httpx - \S+ - HTTP Request"),
    re.compile(r"^httpcore - "),
    re.compile(r"^BLProver\.lemma\.proven_lemma_store - INFO - 已规范化"),
    re.compile(r"^BLProver\.lemma\.definition_store - INFO - 已从 legacy"),
    re.compile(r"^BLProver\.lemma\.unproven_lemma_store - INFO - ChromaDB"),
    re.compile(r"^BLProver\.eval\.proof_difficulty_score(_v2)?\.\w+ - INFO -"),
    re.compile(r"^BLProver\.main - INFO - step\d+_\S+ 完成，输出长度"),
    re.compile(r"^BLProver\.lemma\.unproven_lemma_store - INFO - 引理 \.thy 已写入"),
    re.compile(r"^BLProver\.lemma\.proven_lemma_store - INFO - 已更新 \d+ 条引理质量分"),
    re.compile(r"^BLProver\.lemma\.proven_lemma_store - INFO - 领域 .* 已证引理库"),
    re.compile(r"^\[lemmas-reflection \d+/\d+\] 引理陈述验证通过"),
)

# Python 解释器自身的 unraisable 噪声（asyncio proactor 关闭时的报错块）
_SWALLOW_START_RE = re.compile(r"^Exception ignored in: ")
_SWALLOW_END_RE = re.compile(r"^(\w+\.)*\w*(Error|Warning|Exception): ")


def should_show_console(line: str) -> bool:
    """控制台是否显示该行（verbose 时全部显示）。

    仅按行内容过滤，不改变日志文件内容。
    """
    if _verbose:
        return True
    text = line.strip()
    if not text:
        return True
    for pattern in _INTERNAL_PATTERNS:
        if pattern.match(text):
            return False
    return True


class _SwallowBlock:
    """吞掉 Python 解释器打印的 unraisable 报错块（Exception ignored in: ...）。"""

    def __init__(self):
        self.active = False

    def keep(self, text: str) -> bool:
        if _SWALLOW_START_RE.match(text):
            self.active = True
            return False
        if not self.active:
            return True
        if _SWALLOW_END_RE.match(text):
            self.active = False
        return False


class ConsoleLineFilter:
    """按行过滤写入控制台的内容（日志文件侧不受影响）。"""

    def __init__(self, verbose: bool = False):
        self.verbose = bool(verbose)
        self._buffer = ""
        self._swallow = _SwallowBlock()

    def feed(self, data: str) -> str:
        if self.verbose:
            return data
        self._buffer += data
        visible: List[str] = []
        while True:
            idx = self._buffer.find("\n")
            if idx < 0:
                break
            line = self._buffer[: idx + 1]
            self._buffer = self._buffer[idx + 1 :]
            if not self._swallow.keep(line):
                continue
            if should_show_console(line):
                visible.append(line)
        return "".join(visible)

    def drain(self) -> str:
        """输出尚未成行的残留文本（用于 flush）。"""
        pending = self._buffer
        self._buffer = ""
        if not pending:
            return ""
        return pending if should_show_console(pending) else ""


# ---------------------------------------------------------------------------
# 阶段看板
# ---------------------------------------------------------------------------


def _display_width(text: str) -> int:
    width = 0
    for ch in text:
        width += 2 if _is_wide(ch) else 1
    return width


def _is_wide(ch: str) -> bool:
    code = ord(ch)
    return (
        0x1100 <= code <= 0x115F
        or 0x2E80 <= code <= 0xA4CF
        or 0xAC00 <= code <= 0xD7A3
        or 0xF900 <= code <= 0xFAFF
        or 0xFE30 <= code <= 0xFE6F
        or 0xFF00 <= code <= 0xFF60
        or 0xFFE0 <= code <= 0xFFE6
        or 0x1F300 <= code <= 0x1FAFF
    )


def _pad(text: str, width: int) -> str:
    return text + " " * max(0, width - _display_width(text))


def format_duration(seconds: float) -> str:
    seconds = max(0.0, float(seconds))
    if seconds < 60:
        return "%.1fs" % seconds
    minutes, sec = divmod(int(round(seconds)), 60)
    if minutes < 60:
        return "%dm%02ds" % (minutes, sec)
    hours, minutes = divmod(minutes, 60)
    return "%dh%02dm%02ds" % (hours, minutes, sec)


class StageBoard:
    """阶段进度看板（单定理维度）。"""

    def __init__(self):
        self.enabled = False
        self.theorem_name = ""
        self.domain = ""
        self.attempt = 0
        self.total_attempts = 1
        self._started: Dict[str, float] = {}
        self._elapsed: Dict[str, float] = {}
        self._notes: Dict[str, str] = {}
        self._order: List[str] = []
        self._run_start = 0.0

    # -- 生命周期 ---------------------------------------------------------
    def begin(
        self,
        theorem_name: str,
        *,
        domain: str = "",
        output_dir: str = "",
        attempt: int = 1,
        total_attempts: int = 1,
    ) -> None:
        self.enabled = True
        self.theorem_name = theorem_name
        self.domain = domain
        self.attempt = attempt
        self.total_attempts = total_attempts
        self._started.clear()
        self._elapsed.clear()
        self._notes.clear()
        self._order.clear()
        self._run_start = time.perf_counter()

        self._print("")
        self._print(_LINE)
        title = "BLProver 定理证明 · %s" % theorem_name
        self._print(" " + title)
        meta = " 领域 %s ｜ 共 %d 个阶段" % (domain or "-", TOTAL_STAGES)
        if output_dir:
            meta += " ｜ 输出 %s" % output_dir
        self._print(meta)
        if total_attempts > 1:
            self._print(" 外层尝试 %d/%d" % (attempt, total_attempts))
        self._print(_LINE)

    def start(self, key: str, note: Optional[str] = None) -> None:
        if not self.enabled:
            return
        if key in self._started:
            return
        self._started[key] = time.perf_counter()
        if key not in self._order:
            self._order.append(key)
        suffix = " ｜ %s" % note if note else ""
        self._print(
            "[阶段 %d/%d] 开始：%s%s"
            % (STAGE_INDEX.get(key, 0), TOTAL_STAGES, STAGE_LABEL.get(key, key), suffix)
        )

    def finish(self, key: str, ok: bool = True, note: Optional[str] = None) -> None:
        if not self.enabled:
            return
        start = self._started.pop(key, None)
        if start is not None:
            self._elapsed[key] = time.perf_counter() - start
        if key not in self._order:
            self._order.append(key)
        if note:
            self._notes[key] = note
        mark = "完成 ✓" if ok else "结束 ✗"
        parts = [format_duration(self._elapsed.get(key, 0.0))]
        if note:
            parts.append(note)
        self._print(
            "[阶段 %d/%d] %s ｜ %s"
            % (
                STAGE_INDEX.get(key, 0),
                TOTAL_STAGES,
                mark,
                " ｜ ".join(parts),
            )
        )

    def skip(self, key: str, note: str = "未触发") -> None:
        if not self.enabled:
            return
        if key in self._elapsed:
            return
        self._order.append(key)
        self._notes[key] = note
        self._print(
            "[阶段 %d/%d] 跳过：%s ｜ %s"
            % (STAGE_INDEX.get(key, 0), TOTAL_STAGES, STAGE_LABEL.get(key, key), note)
        )

    def event(self, text: str) -> None:
        if not self.enabled:
            return
        self._print("           " + text)

    # -- 汇总 -------------------------------------------------------------
    def summary(self, *, status: str = "", note: str = "") -> None:
        if not self.enabled:
            return
        elapsed_total = time.perf_counter() - self._run_start
        self._print("")
        self._print(_THIN)
        self._print(" 阶段耗时汇总 · %s" % (self.theorem_name or "-"))
        self._print(_THIN)
        for key, label in STAGES:
            if key in self._elapsed:
                duration = format_duration(self._elapsed[key])
            elif key in self._started:
                duration = "进行中"
            else:
                duration = "-"
            row = " %d/%d %s" % (STAGE_INDEX[key], TOTAL_STAGES, label)
            line = " %s%s" % (_pad(row, 42), duration)
            note_text = self._notes.get(key)
            if note_text and key not in self._started:
                line += "  ｜ %s" % note_text
            self._print(line)
        self._print(_THIN)
        tail = " 合计 %s" % format_duration(elapsed_total)
        if status:
            tail += " ｜ 结果：%s" % status
        self._print(tail)
        if note:
            self._print(" %s" % note)
        self._print(_THIN)

    # -- 内部 -------------------------------------------------------------
    def _print(self, text: str) -> None:
        try:
            sys.stdout.write(text + "\n")
            sys.stdout.flush()
        except Exception:
            try:
                print(text, flush=True)
            except Exception:
                pass


board = StageBoard()


def label_of(key: str) -> str:
    return STAGE_LABEL.get(key, key)