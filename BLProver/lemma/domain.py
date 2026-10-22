"""从定理 JSON / 文件路径解析形式化领域（domain）。"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

_DOMAIN_RE = re.compile(r"^[A-Za-z0-9_]+$")

# 线性数据结构领域，其 theory 产出放在 output/theory/linear_data/<domain>/ 下
LINEAR_DOMAINS = {"boundedstack", "FIFO_queue", "priority_queue", "stack", "sublist", "list"}


def get_domain_group(domain: str) -> str:
    """返回领域所属的父级分组目录名，如 "linear_data"；不在分组内则返回空字符串。"""
    d = normalize_domain(domain)
    if d in LINEAR_DOMAINS:
        return "linear_data"
    return ""


def normalize_domain(name: str) -> str:
    text = (name or "").strip().replace("-", "_")
    if not text or not _DOMAIN_RE.match(text):
        raise ValueError(f"invalid domain name: {name!r}")
    return text


def theorem_theory_dir(
    output_dir: str | Path,
    domain: str,
    theorem_name: str,
) -> Path:
    """定理工作目录：output/theory/[group/]<domain>/<theorem_name>/。"""
    d = normalize_domain(domain)
    name = (theorem_name or "").strip()
    if not name:
        raise ValueError("theorem_name is required")
    group = get_domain_group(d)
    if group:
        return Path(output_dir) / "theory" / group / d / name
    return Path(output_dir) / "theory" / d / name


def is_theorem_output_dir(path: Path) -> bool:
    """是否为单个定理输出目录（含 sketch / unproven / final 等）。"""
    p = Path(path)
    if not p.is_dir():
        return False
    if any(p.glob("*_sketch.thy")):
        return True
    if any(p.glob("*_unproven_lemmas.thy")):
        return True
    thy = p / f"{p.name}.thy"
    return thy.is_file()


def build_theorem_domain_index(data_dir: str | Path) -> dict[str, str]:
    """从 data/<domain>/<theorem>.json 建立 theorem → domain 索引。"""
    root = Path(data_dir)
    index: dict[str, str] = {}
    if not root.is_dir():
        return index
    for json_path in root.rglob("*.json"):
        parts = json_path.parts
        if "data" not in parts:
            continue
        idx = parts.index("data")
        if idx + 1 >= len(parts):
            continue
        domain = parts[idx + 1]
        if domain.startswith(".") or domain in ("miniF2F-main",):
            continue
        theorem = json_path.stem
        index.setdefault(theorem, normalize_domain(domain))
    return index


def resolve_domain(
    theorem_data: Optional[dict] = None,
    theorem_file: Optional[str | Path] = None,
) -> str:
    """
    领域标识，用于 output/theory/<domain>/defs.thy、proven_lemmas.thy
    与 output/theory/<domain>/<theorem>/ 定理输出。

    优先级：JSON 字段 domain > 数据文件父目录名（data/stack/foo.json → stack）。
    """
    data = theorem_data or {}
    explicit = (data.get("domain") or "").strip()
    if explicit:
        return normalize_domain(explicit)

    if theorem_file:
        parts = Path(theorem_file).resolve().parts
        if "data" in parts:
            idx = parts.index("data")
            if idx + 1 < len(parts):
                return normalize_domain(parts[idx + 1])

    raise ValueError(
        "无法解析定理 domain：请在 JSON 中设置 \"domain\"，"
        "或将定理放在 data/<domain>/ 目录下"
    )
