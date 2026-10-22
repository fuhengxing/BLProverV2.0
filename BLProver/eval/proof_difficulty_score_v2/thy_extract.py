"""
从 Isabelle .thy 提取 lemma/theorem 块，供引理使用计数时优先使用含 proof 的完整文本。
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, Optional, Union

from .analyzer import extract_proof_region

_DECL_BLOCK_START = re.compile(
    r"^\s*(lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE,
)


def extract_decl_blocks(thy_text: str) -> Dict[str, str]:
    """解析 thy 文本，返回 {声明名: 完整块文本}。"""
    lines = (thy_text or "").splitlines()
    blocks: Dict[str, str] = {}
    i = 0
    while i < len(lines):
        m = _DECL_BLOCK_START.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(2)
        start = i
        i += 1
        while i < len(lines):
            line = lines[i]
            if _DECL_BLOCK_START.match(line):
                break
            if line.strip() == "end":
                break
            i += 1
        block = "\n".join(lines[start:i]).strip()
        if block:
            blocks[name] = block
    return blocks


def load_decl_blocks_from_thy(thy_path: Path) -> Dict[str, str]:
    if not thy_path.is_file():
        return {}
    return extract_decl_blocks(thy_path.read_text(encoding="utf-8"))


def merge_decl_blocks_from_thy_files(
    sketch_thy_path: Optional[Union[Path, str]] = None,
    unproven_lemmas_path: Optional[Union[Path, str]] = None,
) -> Dict[str, str]:
    """
    合并 sketch / unproven .thy 中的声明块；同名时 unproven 优先（含最新引理证明）。
    """
    merged: Dict[str, str] = {}
    sketch = Path(sketch_thy_path) if sketch_thy_path else None
    unproven = Path(unproven_lemmas_path) if unproven_lemmas_path else None
    if sketch and sketch.is_file():
        merged.update(load_decl_blocks_from_thy(sketch))
    if unproven and unproven.is_file():
        merged.update(load_decl_blocks_from_thy(unproven))
    return merged


def _has_proof_section(text: str) -> bool:
    return bool(extract_proof_region(text or "").strip())


def pick_scoring_text(
    statement: str,
    thy_blocks: Dict[str, str],
    lemma_name: str,
) -> str:
    """
    选取用于统计引理使用的文本：优先 thy 中含 proof 的完整块，否则用 statement。
    """
    thy_block = thy_blocks.get(lemma_name) if lemma_name else None
    stmt = (statement or "").strip()

    if thy_block and _has_proof_section(thy_block):
        return thy_block
    if stmt and _has_proof_section(stmt):
        return stmt
    if thy_block:
        return thy_block
    return stmt


def pick_scoring_text_by_name(
    thy_blocks: Dict[str, str],
    decl_name: str,
) -> Optional[str]:
    block = thy_blocks.get(decl_name)
    if not block:
        return None
    return block
