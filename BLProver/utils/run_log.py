"""运行日志文件命名（按定理名或功能名，不使用时间戳）。"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

_UNSAFE_LOG_STEM_RE = re.compile(r"[^\w\-.]+", re.UNICODE)


def sanitize_log_stem(name: str) -> str:
    """将名称转为安全的日志文件名主干（不含扩展名）。"""
    stem = Path(name).stem if name else "run"
    stem = _UNSAFE_LOG_STEM_RE.sub("_", stem).strip("._")
    return stem or "run"


def run_log_path(log_dir: Path, stem: str) -> Path:
    """在 log_dir 下生成 {stem}.log 路径。"""
    log_dir.mkdir(parents=True, exist_ok=True)
    return log_dir / f"{sanitize_log_stem(stem)}.log"


def resolve_main_run_log_stem(
    *,
    single: Optional[str] = None,
    verify_thy_file: Optional[str] = None,
    data_dir: str = "./data",
) -> str:
    """根据 BLProver.main CLI 参数解析日志主干名。"""
    if single:
        return Path(single).stem
    if verify_thy_file:
        return Path(verify_thy_file).stem
    return f"batch_{Path(data_dir).name}"
