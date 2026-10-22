"""
分析已验证 .thy 中：主定理证明实际引用了哪些构造引理。
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

from ..utils.lemma_dedup import (
    _FACT_HEAD_RE,
    collect_lemma_refs_from_proof,
    extract_fact_name,
)

_SORRY_LINE_RE = re.compile(r"^\s*sorry\s*\.?\s*$", re.IGNORECASE)

_DECL_START_IN_PREAMBLE = re.compile(
    r"^\s*(lemma|theorem|corollary|proposition)\s+",
    re.IGNORECASE,
)


@dataclass
class LemmaUsageEntry:
    name: str
    statement: str
    still_sorry: bool = True
    source: str = "unproven"

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "statement": self.statement,
            "still_sorry": self.still_sorry,
            "source": self.source,
        }


@dataclass
class TheoremLemmaUsageReport:
    theorem_name: str
    thy_path: str
    used: List[LemmaUsageEntry] = field(default_factory=list)
    """proof 中引用且定义在 unproven_lemmas.thy 中的引理（待证候选）。"""
    unused: List[LemmaUsageEntry] = field(default_factory=list)
    """unproven_lemmas.thy 中未被 proof 引用的引理。"""
    external_refs: List[LemmaUsageEntry] = field(default_factory=list)
    """proof 中引用但不在 unproven_lemmas.thy 中的引理（如 proven_lemmas / Main，不迭代证明）。"""
    theorem_proof_preview: str = ""

    def to_dict(self) -> dict:
        return {
            "theorem_name": self.theorem_name,
            "thy_path": self.thy_path,
            "used_lemma_names": [x.name for x in self.used],
            "unused_lemma_names": [x.name for x in self.unused],
            "external_ref_names": [x.name for x in self.external_refs],
            "used": [x.to_dict() for x in self.used],
            "unused": [x.to_dict() for x in self.unused],
            "external_refs": [x.to_dict() for x in self.external_refs],
            # 兼容旧字段名
            "reused_from_proven_names": [x.name for x in self.external_refs],
            "reused_from_proven": [x.to_dict() for x in self.external_refs],
            "theorem_proof_preview": self.theorem_proof_preview,
        }


_FACT_DECL_KINDS = ("theorem", "lemma", "corollary", "proposition")


def _find_main_theorem_line_index(lines: List[str], theorem_name: str) -> Optional[int]:
    for kind in _FACT_DECL_KINDS:
        pat = re.compile(rf"^\s*{kind}\s+{re.escape(theorem_name)}\b", re.IGNORECASE)
        for i, line in enumerate(lines):
            if pat.match(line):
                return i
    # JSON theorem name 与 formal statement 中主 fact 名不一致时，回退到首个主 fact 行
    for kind in _FACT_DECL_KINDS:
        pat = re.compile(rf"^\s*{kind}\s+", re.IGNORECASE)
        for i, line in enumerate(lines):
            if pat.match(line):
                return i
    return None


def extract_main_theorem_proof_region(thy_text: str, theorem_name: str) -> str:
    lines = thy_text.splitlines()
    start = _find_main_theorem_line_index(lines, theorem_name)
    if start is None:
        return ""
    proof_start: Optional[int] = None
    for i in range(start, len(lines)):
        if re.search(r"\bproof\b", lines[i], re.IGNORECASE):
            proof_start = i + 1
            break
    if proof_start is None:
        return "\n".join(lines[start:])

    proof_lines: List[str] = []
    for i in range(proof_start, len(lines)):
        stripped = lines[i].strip()
        if stripped in ("qed", "done", "end"):
            break
        proof_lines.append(lines[i])
    return "\n".join(proof_lines)


def lemma_blocks_in_thy(thy_text: str) -> Dict[str, str]:
    """从 .thy 文本提取全部 lemma/corollary 块（用于 unproven_lemmas.thy）。"""
    blocks: Dict[str, List[str]] = {}
    current_name: Optional[str] = None
    for line in thy_text.splitlines():
        if line.strip() == "end":
            break
        m = _FACT_HEAD_RE.match(line)
        if m and m.group(1).lower() in ("lemma", "corollary", "proposition"):
            current_name = m.group(2)
            blocks[current_name] = [line]
        elif current_name is not None:
            blocks[current_name].append(line)
    return {k: "\n".join(v).strip() for k, v in blocks.items()}


def _lemma_blocks_before_theorem(thy_text: str, theorem_name: str) -> Dict[str, str]:
    lines = thy_text.splitlines()
    cut = _find_main_theorem_line_index(lines, theorem_name)
    preamble_lines = lines if cut is None else lines[:cut]

    blocks: Dict[str, List[str]] = {}
    current_name: Optional[str] = None
    for line in preamble_lines:
        m = _FACT_HEAD_RE.match(line)
        if m and m.group(1).lower() in ("lemma", "corollary", "proposition"):
            current_name = m.group(2)
            blocks[current_name] = [line]
        elif current_name is not None:
            blocks[current_name].append(line)
    return {k: "\n".join(v).strip() for k, v in blocks.items()}


def lemma_still_sorry(block: str) -> bool:
    for line in block.splitlines():
        if _SORRY_LINE_RE.match(line):
            return True
    return False


def analyze_theorem_lemma_usage(
    sketch_thy_path: Path,
    theorem_name: str,
    constructed_statements: List[str],
    *,
    unproven_lemmas_path: Optional[Path] = None,
) -> TheoremLemmaUsageReport:
    """
    分析主定理 proof 引用了哪些引理，并按是否在 unproven_lemmas.thy 中分类。

    - proof 引用 + 在 unproven_lemmas.thy → used（统计用；迭代证明覆盖 unproven 全部 sorry）
    - proof 引用 + 不在 unproven_lemmas.thy → external_refs（不迭代证明）
    - 在 unproven 但 proof 未引用 → unused
    """
    sketch_text = sketch_thy_path.read_text(encoding="utf-8")
    proof_region = extract_main_theorem_proof_region(sketch_text, theorem_name)
    refs = collect_lemma_refs_from_proof(proof_region)

    stmt_by_name: Dict[str, str] = {}
    for stmt in constructed_statements:
        name = extract_fact_name(stmt)
        if name:
            stmt_by_name[name] = stmt.strip()

    if unproven_lemmas_path and unproven_lemmas_path.is_file():
        blocks = lemma_blocks_in_thy(
            unproven_lemmas_path.read_text(encoding="utf-8")
        )
    else:
        blocks = _lemma_blocks_before_theorem(sketch_text, theorem_name)

    unproven_names = set(blocks.keys())
    used_names = sorted(refs & unproven_names)
    unused_names = sorted(unproven_names - refs)
    external_names = sorted(refs - unproven_names)

    used_entries = [
        LemmaUsageEntry(
            name=name,
            statement=stmt_by_name.get(name, blocks.get(name, "")),
            still_sorry=lemma_still_sorry(blocks.get(name, "")),
            source="unproven",
        )
        for name in used_names
    ]
    unused_entries = [
        LemmaUsageEntry(
            name=name,
            statement=stmt_by_name.get(name, blocks.get(name, "")),
            still_sorry=lemma_still_sorry(blocks.get(name, "")),
            source="unproven",
        )
        for name in unused_names
    ]
    external_entries = [
        LemmaUsageEntry(
            name=name,
            statement=stmt_by_name.get(name, ""),
            still_sorry=False,
            source="external",
        )
        for name in external_names
    ]

    preview = proof_region.strip()
    if len(preview) > 2000:
        preview = preview[:2000] + "\n..."

    return TheoremLemmaUsageReport(
        theorem_name=theorem_name,
        thy_path=str(sketch_thy_path),
        used=used_entries,
        unused=unused_entries,
        external_refs=external_entries,
        theorem_proof_preview=preview,
    )
