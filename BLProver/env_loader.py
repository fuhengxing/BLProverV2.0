"""
本地默认配置加载器

从仓库根目录（或当前工作目录）的 `.env` 文件读取环境变量并注入进程环境，
这样 `OPENAI_API_KEY` / `OPENAI_BASE_URL` 只需配置一次，每次启动自动生效。

优先级：真实进程环境变量 > `.env` 文件（已有的环境变量不会被覆盖）。
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Dict, List

ENV_FILE_NAME = ".env"

_loaded = False


def _package_root() -> Path:
    """仓库根目录（BLProver 包的上一级）。"""
    return Path(__file__).resolve().parent.parent


def env_file_candidates() -> List[Path]:
    """按优先级返回候选 `.env` 路径：当前工作目录优先，其次仓库根目录。"""
    candidates: List[Path] = []
    for base in (Path.cwd(), _package_root()):
        path = base / ENV_FILE_NAME
        if path not in candidates:
            candidates.append(path)
    return candidates


def _parse_env_text(text: str) -> Dict[str, str]:
    """极简 `.env` 解析：支持注释、空行、`export` 前缀、单双引号值。"""
    result: Dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export "):].strip()
        if "=" not in line:
            continue
        key, _, value = line.partition("=")
        key = key.strip()
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in ("'", '"'):
            value = value[1:-1]
        if key:
            result[key] = value
    return result


def load_env_file(override: bool = False) -> Dict[str, str]:
    """加载 `.env`（进程内只执行一次；`override=True` 可强制覆盖已有环境变量）。

    Returns:
        实际注入的环境变量键值对（值为原文，调用方不要打印到日志）。
    """
    global _loaded
    if _loaded and not override:
        return {}

    applied: Dict[str, str] = {}
    for path in env_file_candidates():
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8-sig")
        except OSError:
            continue
        for key, value in _parse_env_text(text).items():
            if not override and os.environ.get(key):
                continue
            os.environ[key] = value
            applied[key] = value

    _loaded = True
    return applied


__all__ = ["ENV_FILE_NAME", "env_file_candidates", "load_env_file"]
