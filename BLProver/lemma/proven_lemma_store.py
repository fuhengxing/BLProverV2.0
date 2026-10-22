"""
按领域存放已证引理：output/theory/<domain>/proven_lemmas.thy（imports Main defs，无定义块）。
"""

from __future__ import annotations

import json
import logging
import re
import shutil
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from ..eval.proof_difficulty_score_v2.thy_extract import (
    extract_decl_blocks,
    load_decl_blocks_from_thy,
)
from ..eval.quality_scale import Q_SCALE
from ..utils.lemma_dedup import (
    alpha_key_for_lemma_block,
    build_lemma_merge_proposition_index,
    collect_fact_names_from_sketch,
    extract_fact_name,
    extract_proposition_key,
    find_semantic_duplicate_name,
    retarget_lemma_block_name,
    rewrite_lemma_ref_names,
    topological_sort_lemma_block_names,
)
from .unproven_lemma_store import UnprovenLemmaStore

logger = logging.getLogger(__name__)

from .domain import get_domain_group, normalize_domain
from .thy_imports import PROVEN_THEORY_NAME, domain_defs_imports
_QUALITY_SCORES_FILENAME = "lemma_quality_scores.json"

_LEMMA_HEAD_LINE = re.compile(
    r"^(\s*)(lemma|corollary|proposition)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE,
)
_THEOREM_HEAD_LINE = re.compile(r"^\s*theorem\s+", re.IGNORECASE)
_BEGIN_LINE = re.compile(r"^\s*begin\s*$", re.IGNORECASE)
_DECLARE_QAD = re.compile(r"^\s*declare\s+\[\[quick_and_dirty", re.IGNORECASE)
_DEF_CHUNK_START = re.compile(
    r"^\s*(type_synonym|abbreviation|definition|fun|primrec|locale|typedecl|datatype|typedef)\b",
    re.IGNORECASE,
)
_TYPE_SYNONYM_START = re.compile(r"^\s*type_synonym\b", re.IGNORECASE)


def _quality_scores_path(output_dir: str | Path) -> Path:
    return (
        Path(output_dir) / "results" / "proven_lemmas" / _QUALITY_SCORES_FILENAME
    )


def _load_quality_scores(output_dir: str | Path) -> Dict[str, dict]:
    """加载 {lemma_name: {s: int, d: int, u: int, q: float}}。"""
    path = _quality_scores_path(output_dir)
    if not path.is_file():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        logger.warning("加载质量分文件失败: %s", exc)
        return {}


def _save_quality_scores(
    output_dir: str | Path, scores: Dict[str, dict]
) -> None:
    path = _quality_scores_path(output_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(scores, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8",
    )


def _compute_q(s: int, d: int, u: int) -> float:
    """Q(i) = Q_SCALE * U(i) * D(i) / S(i)，S=0 时返回 0（Q_SCALE 见 eval/quality_scale.py）。"""
    if s <= 0:
        return 0.0
    return round(Q_SCALE * (u * d) / s, 4)


class ProvenLemmaStore:
    """跨定理共享的已证引理 .thy 读写与同步。"""

    @staticmethod
    def domain_dir(output_dir: str | Path, domain: str) -> Path:
        d = normalize_domain(domain)
        group = get_domain_group(d)
        if group:
            return Path(output_dir) / "theory" / group / d
        return Path(output_dir) / "theory" / d

    @staticmethod
    def proven_thy_path(output_dir: str | Path, domain: str) -> Path:
        return ProvenLemmaStore.domain_dir(output_dir, domain) / f"{PROVEN_THEORY_NAME}.thy"

    @staticmethod
    def proven_lemma_names(output_dir: str | Path, domain: str) -> set[str]:
        path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
        if not path.is_file():
            return set()
        return set(load_decl_blocks_from_thy(path).keys())

    @staticmethod
    def filter_lemmas_not_in_proven_library(
        statements: Sequence[str],
        output_dir: str | Path,
        domain: str,
    ) -> List[str]:
        """去掉名称已在领域 proven_lemmas.thy 中的引理，避免 import 冲突。"""
        proven_names = ProvenLemmaStore.proven_lemma_names(output_dir, domain)
        if not proven_names:
            return list(statements)
        filtered: List[str] = []
        dropped: List[str] = []
        for stmt in statements:
            name = extract_fact_name(stmt)
            if name and name in proven_names:
                dropped.append(name)
                continue
            filtered.append(stmt)
        if dropped:
            logger.info(
                "跳过与 proven_lemmas 重名的 unproven 引理: %s",
                ", ".join(sorted(dropped)),
            )
        return filtered

    @staticmethod
    def global_thy_path(output_dir: str | Path, domain: str) -> Path:
        """兼容名：返回领域 proven_lemmas.thy 路径。"""
        return ProvenLemmaStore.proven_thy_path(output_dir, domain)

    @staticmethod
    def ensure_global(output_dir: str | Path, domain: str) -> Path:
        from .definition_store import DefinitionStore

        DefinitionStore.ensure_domain(output_dir, domain)
        DefinitionStore.migrate_legacy_root_defs(output_dir)
        DefinitionStore.migrate_legacy_proven_split(output_dir, domain=domain)
        path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
        if not path.is_file():
            ProvenLemmaStore.write_proven_thy(path, [])
        return path

    @staticmethod
    def is_session_proven_thy(thy_text: str, *, path: Optional[Path] = None) -> bool:
        """旧版定理目录 session proven（已废弃，仅用于迁移识别）。"""
        if path is not None:
            p = Path(path)
            if p.name == f"{PROVEN_THEORY_NAME}.thy":
                from .thy_imports import DEFS_THEORY_NAME

                if (p.parent / f"{DEFS_THEORY_NAME}.thy").is_file():
                    return False
                if any(p.parent.glob("*_sketch.thy")) or any(
                    p.parent.glob("*_unproven_lemmas.thy")
                ):
                    return True
        return bool(
            re.search(r'imports\s+[^\n]*_unproven_lemmas"', thy_text or "", re.I)
        )

    @staticmethod
    def list_lemma_only_blocks_from_text(thy_text: str) -> List[str]:
        blocks: List[str] = []
        for block in extract_decl_blocks(thy_text).values():
            first = (block or "").strip().splitlines()[0] if block else ""
            if _LEMMA_HEAD_LINE.match(first):
                blocks.append(block)
        return blocks

    @staticmethod
    def reconcile_thy_from_unproven_source(
        proven_path: Path,
        unproven_thy_text: str,
        output_dir: str | Path,
    ) -> bool:
        """
        按 proven 内引理证明所依赖的事实，从 unproven 补全全局 defs.thy。
        返回是否写回 defs 或规范化 proven。
        """
        from .definition_store import DefinitionStore

        if not proven_path.is_file():
            return False
        text = proven_path.read_text(encoding="utf-8")
        if ProvenLemmaStore.is_session_proven_thy(text, path=proven_path):
            return ProvenLemmaStore.normalize_thy_file(proven_path)
        source_defs = ProvenLemmaStore.extract_definitions_preamble(unproven_thy_text)
        blocks = [
            b
            for b in extract_decl_blocks(text).values()
            if _LEMMA_HEAD_LINE.match(
                ((b or "").strip().splitlines()[0] if b else "")
            )
        ]
        if not blocks:
            return ProvenLemmaStore.normalize_thy_file(proven_path)
        target_domain = (
            proven_path.parent.name
            if proven_path.parent.name != "theory"
            else "priority_queue"
        )
        changed = DefinitionStore.ensure_definitions_for_lemma_blocks(
            output_dir, target_domain, blocks, source_preamble=source_defs
        )
        return changed or ProvenLemmaStore.normalize_thy_file(proven_path)

    @staticmethod
    def sync_global_proven(
        output_dir: str | Path,
        domain: str,
        theorem_dir: Optional[Path] = None,
        *,
        unproven_text: Optional[str] = None,
    ) -> Path:
        """维护领域 proven（仅引理，imports Main defs）。"""
        global_path = ProvenLemmaStore.ensure_global(output_dir, domain)
        if theorem_dir is not None:
            if unproven_text is None:
                for unproven_path in sorted(theorem_dir.glob("*_unproven_lemmas.thy")):
                    try:
                        unproven_text = unproven_path.read_text(encoding="utf-8")
                    except OSError:
                        continue
                    break
            if unproven_text:
                ProvenLemmaStore.reconcile_thy_from_unproven_source(
                    global_path, unproven_text, output_dir
                )
        ProvenLemmaStore.normalize_thy_file(global_path)
        return global_path

    @staticmethod
    def sync_to_theorem_dir(
        output_dir: str | Path, theorem_dir: Path, domain: str
    ) -> Path:
        """
        同步领域 defs + proven；定理目录仅保留 sketch/unproven/final。
        删除旧版 session proven_lemmas.thy 副本。
        """
        from .definition_store import DefinitionStore

        theorem_dir.mkdir(parents=True, exist_ok=True)
        DefinitionStore.ensure_domain(output_dir, domain)
        DefinitionStore.migrate_legacy_root_defs(output_dir)
        DefinitionStore.migrate_legacy_proven_split(output_dir, domain=domain)
        unproven_thy_name = f"{theorem_dir.name}_unproven_lemmas"
        unproven_path = theorem_dir / f"{unproven_thy_name}.thy"
        unproven_text: Optional[str] = None
        if unproven_path.is_file():
            try:
                unproven_text = unproven_path.read_text(encoding="utf-8")
            except OSError:
                unproven_text = None
        ProvenLemmaStore.sync_global_proven(
            output_dir, domain, theorem_dir, unproven_text=unproven_text
        )
        session_proven = theorem_dir / f"{PROVEN_THEORY_NAME}.thy"
        if session_proven.is_file():
            session_proven.unlink()
            logger.info("已删除旧版 session proven: %s", session_proven)
        return ProvenLemmaStore.proven_thy_path(output_dir, domain)

    @staticmethod
    def list_lemma_blocks(output_dir: str | Path, domain: str) -> List[str]:
        path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
        if not path.is_file():
            return []
        return list(load_decl_blocks_from_thy(path).values())

    @staticmethod
    def extract_definitions_preamble(thy_text: str) -> str:
        """提取 begin 之后、首个 lemma/theorem 之前的定义块。"""
        lines = (thy_text or "").splitlines()
        out: List[str] = []
        past_begin = False
        for line in lines:
            if _BEGIN_LINE.match(line):
                past_begin = True
                continue
            if not past_begin:
                continue
            if _DECLARE_QAD.match(line):
                continue
            if line.strip() == "end":
                break
            if _LEMMA_HEAD_LINE.match(line) or _THEOREM_HEAD_LINE.match(line):
                break
            out.append(line)
        return "\n".join(out).strip()

    @staticmethod
    def _strip_stray_end_lines(text: str) -> str:
        """去掉独立的 end 行（不应出现在 definitions / lemma 块内部）。"""
        lines = [
            ln
            for ln in (text or "").splitlines()
            if ln.strip().lower() != "end"
        ]
        return "\n".join(lines).strip()

    @staticmethod
    def _qualify_shadowed_fun_refs_in_definitions(
        preamble: str,
        *,
        theory_name: str = "defs",
    ) -> str:
        """
        fun/primrec 方程 RHS 若引用同文件内先前定义的函数名，Isabelle 会将其解析为
        模式变量（Variable occurs on right hand side only）。对 RHS 中的先前函数名加理论限定。
        """
        if not (preamble or "").strip():
            return preamble or ""

        def _qualify_rhs_line(line: str, shadow_names: set[str]) -> str:
            if "=" not in line:
                return line
            idx = line.index("=")
            lhs, rhs = line[:idx], line[idx:]
            for name in sorted(shadow_names, key=len, reverse=True):
                pattern = (
                    rf"(?<!\.)(?<!{re.escape(theory_name)}\.)"
                    rf"\b{re.escape(name)}\b(?=\s+[\w(])"
                )
                rhs = re.sub(pattern, f"{theory_name}.{name}", rhs)
            return lhs + rhs

        prior_names: set[str] = set()
        out_chunks: List[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(preamble):
            text = chunk.strip()
            if not text:
                continue
            first_line = text.splitlines()[0]
            is_fun = bool(
                re.match(r"\s*(?:fun|primrec)\s+", first_line, re.IGNORECASE)
            )
            if is_fun and prior_names:
                shadow_names = prior_names - ProvenLemmaStore._chunk_defining_names(text)
                if shadow_names:
                    text = "\n".join(
                        _qualify_rhs_line(ln, shadow_names)
                        for ln in text.splitlines()
                    )
            out_chunks.append(text)
            prior_names |= ProvenLemmaStore._chunk_defining_names(text)
        return "\n\n".join(out_chunks).strip()

    @staticmethod
    def _sanitize_isabelle_symbols(text: str) -> str:
        """将 JSON/LLM 中的 Unicode 逻辑符号替换为 Isabelle ASCII 转义。"""
        if not text:
            return text
        replacements = {
            "\u27f7": "\\<longleftrightarrow>",  # ⟷
            "\u27fa": "\\<longleftrightarrow>",  # ⟺
            "\u2194": "\\<longleftrightarrow>",  # ↔
            "\u21d4": "\\<Leftrightarrow>",  # ⇔
            "\u21d2": "\\<Rightarrow>",  # ⇒（类型箭头；勿用 \\<Longrightarrow>）
            "\u2192": "\\<Rightarrow>",  # →
            "\u2264": "\\<le>",  # ≤
            "\u2265": "\\<ge>",  # ≥
            "\u2260": "\\<noteq>",  # ≠
            "\u2227": "\\<and>",  # ∧
            "\u2228": "\\<or>",  # ∨
            "\u00ac": "\\<not>",  # ¬
            "\u2208": "\\<in>",  # ∈
            "\u2209": "\\<notin>",  # ∉
            "\u2026": "...",  # … (calculation step ellipsis)
        }
        out = text
        for char, esc in replacements.items():
            out = out.replace(char, esc)
        return out

    @staticmethod
    def _sanitize_lemma_blocks(blocks: Sequence[str]) -> List[str]:
        out: List[str] = []
        for block in blocks:
            cleaned = ProvenLemmaStore._strip_stray_end_lines(block or "")
            cleaned = ProvenLemmaStore._sanitize_isabelle_symbols(cleaned)
            if cleaned:
                out.append(cleaned)
        return out

    @staticmethod
    def normalize_thy_text(text: str) -> str:
        """
        规范化 .thy：begin 之后正文里移除所有 end，文件末尾只保留一个 end。
        修复历史坏文件中「双 end」或定义区夹杂 end 的问题。
        """
        lines = (text or "").splitlines()
        if not lines:
            return ""
        begin_idx = next(
            (i for i, ln in enumerate(lines) if _BEGIN_LINE.match(ln)),
            None,
        )
        if begin_idx is None:
            return (text or "").rstrip() + "\n"

        header = lines[: begin_idx + 1]
        body: List[str] = []
        for ln in lines[begin_idx + 1 :]:
            if ln.strip().lower() == "end":
                continue
            body.append(ln)
        while body and not body[-1].strip():
            body.pop()

        parts: List[str] = list(header)
        if body:
            if parts and parts[-1].strip():
                parts.append("")
            parts.extend(body)
        parts.append("end")
        return "\n".join(parts) + "\n"

    @staticmethod
    def normalize_thy_file(path: Path) -> bool:
        """若文件被规范化则写回。返回是否发生修改。"""
        if not path.is_file():
            return False
        raw = path.read_text(encoding="utf-8")
        normalized = ProvenLemmaStore.normalize_thy_text(raw)
        if normalized != raw:
            path.write_text(normalized, encoding="utf-8")
            logger.info("已规范化 proven .thy 结构: %s", path)
            return True
        return False

    @staticmethod
    def _split_definition_chunks(preamble: str) -> List[str]:
        chunks: List[str] = []
        current: List[str] = []
        for line in (preamble or "").splitlines():
            if line.strip().lower() == "end":
                continue
            if _DEF_CHUNK_START.match(line) and current:
                text = "\n".join(current).strip()
                if text:
                    chunks.append(text)
                current = [line]
            else:
                current.append(line)
        if current:
            text = "\n".join(current).strip()
            if text:
                chunks.append(text)
        return chunks

    @staticmethod
    def _definition_chunk_tier(chunk: str) -> int:
        """
        定义块层级：other formal（datatype/type_synonym 等）→ fun/primrec → definition → abbreviation。
        """
        line = (chunk or "").strip().splitlines()[0] if chunk else ""
        stripped = line.strip()
        if re.match(
            r"(?:datatype|type_synonym|typedecl|typedef|locale)\b",
            stripped,
            re.IGNORECASE,
        ):
            return 0
        if re.match(r"abbreviation\s+", stripped, re.IGNORECASE):
            return 3
        if not ProvenLemmaStore._chunk_defining_names(chunk):
            return 0
        if re.match(r"definition\s+", stripped, re.IGNORECASE):
            return 2
        if re.match(r"(?:fun|primrec)\s+", stripped, re.IGNORECASE):
            return 1
        return 1

    @staticmethod
    def _chunk_referenced_names(chunk: str, candidate_names: set[str]) -> set[str]:
        """扫描定义块正文，返回它引用到的候选名集合（含 theory.name 限定形式）。"""
        text = chunk or ""
        if not candidate_names or not text:
            return set()
        refs: set[str] = set()
        for name in candidate_names:
            if not name:
                continue
            pattern = rf"(?<![\w'])\b{re.escape(name)}\b(?![\w'])"
            if re.search(pattern, text):
                refs.add(name)
        return refs

    @staticmethod
    def sort_definition_preamble(
        preamble: str,
        function_names: Optional[Sequence[str]] = None,
    ) -> str:
        chunks = [
            c.strip()
            for c in ProvenLemmaStore._split_definition_chunks(preamble)
            if c.strip()
        ]
        if not chunks:
            return ""
        name_order = {
            name: idx for idx, name in enumerate(function_names or []) if name
        }

        # 每块的 tier、定义名、引用名
        tiers = [ProvenLemmaStore._definition_chunk_tier(c) for c in chunks]
        def_names = [ProvenLemmaStore._chunk_defining_names(c) for c in chunks]
        all_def_names = set().union(*def_names) if def_names else set()

        # 依赖图：j 必须在 i 之前，当 i 引用了 j 定义的名（且非自身）。
        # 这样可避免把引用了尚未定义函数的块排到前面（前向引用在 Isabelle 里会报
        # "Undefined constant"），例如 complete 引用 height 时 height 须在前。
        deps: list[set[int]] = []
        for i, chunk in enumerate(chunks):
            others = all_def_names - def_names[i]
            refs = ProvenLemmaStore._chunk_referenced_names(chunk, others)
            dep_idx = {
                j for j, names_j in enumerate(def_names)
                if j != i and (names_j & refs)
            }
            deps.append(dep_idx)

        def _tie_key(i: int) -> tuple[int, int, int]:
            rank = (
                min(name_order.get(n, 10**6) for n in def_names[i])
                if def_names[i] and name_order else i
            )
            return (tiers[i], rank, i)

        # Kahn 拓扑排序，tie-break 用 (tier, function_names rank, idx)。
        placed: list[int] = []
        placed_set: set[int] = set()
        n = len(chunks)
        while len(placed) < n:
            ready = [
                i for i in range(n)
                if i not in placed_set and deps[i] <= placed_set
            ]
            if not ready:
                # 出现循环（互递归等）：强制取出优先级最高者以打破死锁。
                ready = [i for i in range(n) if i not in placed_set]
            nxt = min(ready, key=_tie_key)
            placed.append(nxt)
            placed_set.add(nxt)

        return "\n\n".join(chunks[i] for i in placed).strip()

    @staticmethod
    def dedupe_definition_preamble(
        preamble: str,
        function_names: Optional[Sequence[str]] = None,
    ) -> str:
        """按定义名 / type_synonym 名去重，保留首次出现的块。"""
        seen_names: set[str] = set()
        unique: List[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(preamble):
            text = chunk.strip()
            if not text or text.lower() == "end":
                continue
            names = ProvenLemmaStore._chunk_defining_names(text)
            if not names:
                if text not in unique:
                    unique.append(text)
                continue
            if names & seen_names:
                continue
            unique.append(text)
            seen_names |= names
        return ProvenLemmaStore.sort_definition_preamble(
            "\n\n".join(unique).strip(),
            function_names=function_names,
        )

    @staticmethod
    def merge_definition_preambles(
        existing: str,
        new: str,
        function_names: Optional[Sequence[str]] = None,
    ) -> str:
        """合并定义块，按定义名去重（避免 pop/push 等重复声明）。"""
        parts = [(existing or "").strip(), (new or "").strip()]
        combined = "\n\n".join(p for p in parts if p)
        return ProvenLemmaStore.dedupe_definition_preamble(
            combined, function_names=function_names
        )

    @staticmethod
    def _base_names_from_fact_ref(name: str) -> set[str]:
        """将 emp_def、pop.simps 等引用名归约到定义名 emp、pop。"""
        bases: set[str] = set()
        text = (name or "").strip()
        if not text:
            return bases
        bases.add(text)
        if "." in text:
            bases.add(text.split(".", 1)[0])
        if text.endswith("_def") and len(text) > 4:
            bases.add(text[:-4])
        if text.endswith("_simps") and len(text) > 6:
            bases.add(text[:-6])
        return bases

    @staticmethod
    def _chunk_defining_names(chunk: str) -> set[str]:
        """从定义块首行提取被定义的名称。"""
        line = (chunk or "").strip().splitlines()[0] if chunk else ""
        names: set[str] = set()
        m = re.match(r'\s*definition\s+"([^"\s]+)', line, re.IGNORECASE)
        if m:
            names.add(m.group(1))
        m = re.match(
            r"\s*(?:definition|fun|primrec)\s+([A-Za-z0-9_']+)",
            line,
            re.IGNORECASE,
        )
        if m:
            names.add(m.group(1))
        m = re.match(
            r"\s*type_synonym\s+(?:'[\w]+\s+)?(\w+)\s*=",
            line,
            re.IGNORECASE,
        )
        if m:
            names.add(m.group(1))
        m = re.match(r'\s*abbreviation\s+"([^"\s]+)', line, re.IGNORECASE)
        if m:
            names.add(m.group(1))
        m = re.match(
            r"\s*abbreviation\s+([A-Za-z0-9_']+)\s*::", line, re.IGNORECASE
        )
        if m:
            names.add(m.group(1))
        m = re.match(
            r"\s*abbreviation\s+([A-Za-z0-9_']+)\s+where", line, re.IGNORECASE
        )
        if m:
            names.add(m.group(1))
        m = re.search(
            r"typedef\s+(?:\([^)]*\)\s+)*?(?:\([^)]*\)\s+)?(\w+)\s*$",
            (chunk or "").strip(),
            re.IGNORECASE | re.MULTILINE,
        )
        if m:
            names.add(m.group(1))
        return names

    @staticmethod
    def definition_names_in_preamble(preamble: str) -> set[str]:
        names: set[str] = set()
        for chunk in ProvenLemmaStore._split_definition_chunks(preamble):
            names |= ProvenLemmaStore._chunk_defining_names(chunk)
        return names

    @staticmethod
    def preamble_chunks_not_in_proven(
        source_preamble: str,
        proven_preamble: str,
    ) -> str:
        """从 source 中保留 proven 尚未收录的定义块（按定义名去重）。"""
        proven_names = ProvenLemmaStore.definition_names_in_preamble(proven_preamble)
        kept: List[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(source_preamble):
            text = chunk.strip()
            if not text:
                continue
            names = ProvenLemmaStore._chunk_defining_names(text)
            if names and names & proven_names:
                continue
            kept.append(text)
        return "\n\n".join(kept).strip()

    @staticmethod
    def merge_session_definitions(
        global_preamble: str,
        unproven_preamble: str,
    ) -> str:
        """session/global proven 定义区：全局为主，追加 unproven 中尚未出现的定义。"""
        extra = ProvenLemmaStore.preamble_chunks_not_in_proven(
            unproven_preamble, global_preamble
        )
        return ProvenLemmaStore.merge_definition_preambles(global_preamble, extra)

    @staticmethod
    def definition_names_merged_from_unproven(
        global_preamble: str,
        unproven_preamble: str,
    ) -> set[str]:
        """unproven 中实际并入 session/global proven 的定义名（同名冲突的不算）。"""
        extra = ProvenLemmaStore.preamble_chunks_not_in_proven(
            unproven_preamble, global_preamble
        )
        return ProvenLemmaStore.definition_names_in_preamble(extra)

    @staticmethod
    def preamble_chunks_not_merged_into_proven(
        source_preamble: str,
        merged_names: set[str],
    ) -> str:
        """保留 source 中尚未被并入 proven 的定义块（按 merged_names 判定）。"""
        if not merged_names:
            return (source_preamble or "").strip()
        kept: List[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(source_preamble):
            text = chunk.strip()
            if not text:
                continue
            names = ProvenLemmaStore._chunk_defining_names(text)
            if names and names <= merged_names:
                continue
            kept.append(text)
        return "\n\n".join(kept).strip()

    @staticmethod
    def strip_definitions_covered_by_proven(
        unproven_path: Path,
        global_preamble: str,
    ) -> bool:
        """
        从 unproven .thy 移除已并入 session proven 的定义块，避免 sketch 双 import 重复声明。
        仅剥离 unproven→proven 实际合并的定义；与 global 同名但未合并的定义（如 stack pop vs PQ pop）保留。
        """
        if not unproven_path.is_file():
            return False
        text = unproven_path.read_text(encoding="utf-8")
        unproven_defs = ProvenLemmaStore.extract_definitions_preamble(text)
        if not unproven_defs.strip():
            return False
        merged_names = ProvenLemmaStore.definition_names_merged_from_unproven(
            global_preamble, unproven_defs
        )
        if not merged_names:
            return False
        remaining_defs = ProvenLemmaStore.preamble_chunks_not_merged_into_proven(
            unproven_defs, merged_names
        )
        if remaining_defs.strip() == unproven_defs.strip():
            return False
        imports_m = re.search(r"^imports\s+(.+)$", text, re.I | re.M)
        packages = (imports_m.group(1).strip() if imports_m else "Main")
        theory_m = re.search(r'^theory\s+"([^"]+)"', text, re.I | re.M)
        theory_name = theory_m.group(1) if theory_m else unproven_path.stem
        lemma_blocks = ProvenLemmaStore.list_lemma_only_blocks_from_text(text)
        UnprovenLemmaStore.write_unproven_lemma_thy(
            unproven_path,
            lemma_blocks,
            theory_name,
            packages=packages,
            quick_and_dirty=True,
            definitions_block=remaining_defs,
        )
        logger.info(
            "已从 %s 移除已并入 proven 的定义（保留 %d 块）",
            unproven_path,
            len(ProvenLemmaStore._split_definition_chunks(remaining_defs)),
        )
        return True

    @staticmethod
    def definitions_required_for_blocks(lemma_blocks: Sequence[str]) -> set[str]:
        """汇总引理证明体中引用到的事实/定义名（已归约到定义基名）。"""
        required: set[str] = set()
        for block in lemma_blocks:
            for ref in collect_fact_names_from_sketch(block or ""):
                required |= ProvenLemmaStore._base_names_from_fact_ref(ref)
        return required

    @staticmethod
    def pick_definition_chunks(
        source_preamble: str,
        required_names: set[str],
        *,
        already_merged: str = "",
    ) -> str:
        """
        从 source（通常来自 unproven 的 definitions 区）挑选覆盖 required_names 的定义块。
        若需要任意定义，则同时纳入全部 type_synonym（避免 'a stack 等类型未声明）。
        """
        if not (source_preamble or "").strip() or not required_names:
            return ""
        covered: set[str] = set()
        for chunk in ProvenLemmaStore._split_definition_chunks(already_merged or ""):
            covered |= ProvenLemmaStore._chunk_defining_names(chunk)
        picked: List[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(source_preamble):
            text = chunk.strip()
            if not text:
                continue
            names = ProvenLemmaStore._chunk_defining_names(text)
            if names & covered:
                continue
            if _TYPE_SYNONYM_START.match(text):
                if required_names:
                    picked.append(text)
                    covered |= names
                continue
            if names & required_names:
                picked.append(text)
                covered |= names
        return "\n\n".join(picked).strip()

    @staticmethod
    def ensure_definitions_for_lemma_blocks(
        existing_preamble: str,
        source_preamble: str,
        lemma_blocks: Sequence[str],
    ) -> str:
        """在已有 preamble 上，按引理依赖从 source 补全缺失定义块。"""
        required = ProvenLemmaStore.definitions_required_for_blocks(lemma_blocks)
        if not required:
            return (existing_preamble or "").strip()
        picked = ProvenLemmaStore.pick_definition_chunks(
            source_preamble,
            required,
            already_merged=existing_preamble,
        )
        merged = ProvenLemmaStore.merge_definition_preambles(
            existing_preamble, picked
        )
        return ProvenLemmaStore.dedupe_definition_preamble(merged)

    @staticmethod
    def write_proven_thy(
        path: Path,
        lemma_blocks: Sequence[str],
        *,
        definitions_block: str = "",
    ) -> None:
        """写 proven_lemmas.thy：仅引理，imports Main defs。"""
        if (definitions_block or "").strip():
            from .definition_store import DefinitionStore

            domain = path.parent.name
            output_root = path.parent.parent.parent
            DefinitionStore.merge_definitions_block(
                output_root, domain, definitions_block
            )
        blocks = ProvenLemmaStore._sanitize_lemma_blocks(lemma_blocks)
        content = f'''theory "{PROVEN_THEORY_NAME}"
imports {domain_defs_imports()}
begin

'''
        for block in blocks:
            text = (block or "").strip()
            if text:
                content += f"{text}\n\n"
        content += "end\n"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        ProvenLemmaStore.normalize_thy_file(path)

    @staticmethod
    def read_quality_scores(output_dir: str | Path) -> Dict[str, dict]:
        """公开读取持久化质量分 {lemma_name: {s, d, u, q}}。"""
        return _load_quality_scores(output_dir)

    @staticmethod
    def compute_and_save_quality_scores(
        output_dir: str | Path,
        domain: str,
        *,
        syntax_results: Optional[Dict[str, int]] = None,
        proof_difficulty_results: Optional[Dict[str, int]] = None,
        reuse_counts: Optional[Dict[str, int]] = None,
    ) -> Dict[str, dict]:
        """
        合并后重新计算所有引理的 S(i)、D(i)、U(i)、Q(i) 并持久化。

        :param syntax_results: {lemma_name: S(i)}，论文 3.1.3 的四子维度加权值
        :param proof_difficulty_results: {lemma_name: D(i)}，论文 3.1.1 的依赖闭包值
        :param reuse_counts: {lemma_name: U(i)}，论文 3.1.2 的 1+|直接调用者|，若 None 则 U(i)=1
        :returns: {lemma_name: {s, d, u, q}}
        """
        try:
            from ..eval.lemma_reuse import LemmaUsageHistory
        except ImportError:
            LemmaUsageHistory = None  # type: ignore[misc, assignment]

        history = LemmaUsageHistory(output_dir) if LemmaUsageHistory else None
        cached = _load_quality_scores(output_dir)
        scores: Dict[str, dict] = {}

        blocks = ProvenLemmaStore.list_lemma_blocks(output_dir, domain)

        for block in blocks:
            name = extract_fact_name(block)
            if not name:
                continue
            prev = cached.get(name, {})
            if syntax_results is not None:
                s = syntax_results.get(name, prev.get("s", 0))
            else:
                s = prev.get("s", 0)
            if proof_difficulty_results is not None:
                d = proof_difficulty_results.get(name, prev.get("d", 1))
            else:
                d = prev.get("d", 1)
            if reuse_counts is not None:
                u = reuse_counts.get(name, prev.get("u", 1))
            elif history is not None:
                u = history.get_reuse_count(name)
            else:
                u = prev.get("u", 1)
            if u <= 0:
                u = 1
            if d <= 0:
                d = 1
            q = _compute_q(s, d, u)
            scores[name] = {"s": s, "d": d, "u": u, "q": q}

        _save_quality_scores(output_dir, scores)
        total = len(scores)
        q_vals = [v["q"] for v in scores.values()]
        has_s = syntax_results is not None or any(v.get("s", 0) > 0 for v in scores.values())
        if has_s and q_vals:
            logger.info(
                "已更新 %d 条引理质量分 Q(i)；Q_min=%s, Q_max=%s, Q_mean=%s",
                total,
                round(min(q_vals), 4),
                round(max(q_vals), 4),
                round(sum(q_vals) / len(q_vals), 4),
            )
        else:
            logger.info(
                "已刷新 %d 条引理 U(i)（S/D 沿用缓存，完整 Q(i) 待质量评估后写入）",
                total,
            )
        return scores

    @staticmethod
    def referenced_lemma_blocks(
        output_dir: str | Path, domain: str, theorem_text: str
    ) -> List[str]:
        """
        返回定理直接/间接引用的库内引理块（按依赖顺序拓扑排序）。

        供最终定理 .thy 自包含内联：被引用的引理与成功证明的定理同置一个文件，
        该文件只 imports Main，不导入自定义引理库。
        """
        from ..eval.dependency_graph import library_direct_dependencies
        from ..eval.proof_difficulty_score_v2.analyzer import (
            extract_used_lemma_names,
        )
        from ..utils.lemma_dedup import collect_lemma_refs_from_proof

        path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
        if not path.is_file():
            return []
        blocks = extract_decl_blocks(path.read_text(encoding="utf-8"))
        if not blocks:
            return []
        direct = library_direct_dependencies(blocks)
        refs: set[str] = set(extract_used_lemma_names(theorem_text or ""))
        try:
            refs.update(collect_lemma_refs_from_proof(theorem_text or ""))
        except Exception:
            pass
        seen: set[str] = set()
        queue = [r for r in refs if r in blocks]
        while queue:
            cur = queue.pop()
            if cur in seen or cur not in blocks:
                continue
            seen.add(cur)
            queue.extend(d for d in direct.get(cur, ()) if d in blocks)
        if not seen:
            return []
        subset = {n: blocks[n] for n in seen}
        order = topological_sort_lemma_block_names(
            subset, prefer_order=sorted(seen)
        )
        return [subset[n] for n in order if n in subset]

    @staticmethod
    def lemma_identifier_path(output_dir: str | Path, domain: str) -> Path:
        """论文 2.4.1：已证引理唯一递增标识符的持久化路径。"""
        return (
            Path(output_dir)
            / "results"
            / "proven_lemmas"
            / f"lemma_identifiers_{normalize_domain(domain)}.json"
        )

    @staticmethod
    def load_lemma_identifiers(
        output_dir: str | Path, domain: str
    ) -> Dict[str, int]:
        path = ProvenLemmaStore.lemma_identifier_path(output_dir, domain)
        if not path.is_file():
            return {}
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return {}
        if not isinstance(data, dict):
            return {}
        return {
            str(k): int(v)
            for k, v in data.items()
            if isinstance(v, (int, float))
        }

    @staticmethod
    def assign_lemma_identifiers(
        output_dir: str | Path, domain: str, names: Sequence[str]
    ) -> Dict[str, int]:
        """为尚未登记的新引理按给定顺序分配递增标识符并持久化。"""
        path = ProvenLemmaStore.lemma_identifier_path(output_dir, domain)
        data = ProvenLemmaStore.load_lemma_identifiers(output_dir, domain)
        next_id = (max(data.values()) + 1) if data else 1
        changed = False
        for name in names or ():
            if name and name not in data:
                data[name] = next_id
                next_id += 1
                changed = True
        if changed:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(data, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
        return data

    @staticmethod
    def load_quality_scores(output_dir: str | Path) -> Dict[str, dict]:
        """读取已持久化的引理质量分 {name: {s, d, u, q, ...}}。"""
        return _load_quality_scores(output_dir)

    @staticmethod
    def save_quality_scores(
        output_dir: str | Path, scores: Dict[str, dict]
    ) -> None:
        """写回引理质量分（论文 3.1 评分 + 3.2 衰减后的 Q(i)）。"""
        _save_quality_scores(output_dir, scores)

    @staticmethod
    def merge_proven_blocks(
        output_dir: str | Path,
        domain: str,
        new_blocks: Sequence[str],
        *,
        source_theorem: str = "",
        definitions_block: str = "",
        syntax_results: Optional[Dict[str, int]] = None,
        proof_difficulty_results: Optional[Dict[str, int]] = None,
        reuse_counts: Optional[Dict[str, int]] = None,
        similarity_threshold: float = 0.92,
        local_lemma_names: Optional[Sequence[str]] = None,
    ) -> tuple[int, Dict[str, str]]:
        """
        将新证引理合并进领域 proven_lemmas.thy；定义写入同领域 defs.thy。

        similarity_threshold：论文 2.4.2 的矢量判重阈值（余弦相似度 >= 该值视为语义重复）。

        返回 (updated_count, alias_map)：alias_map 将因语义去重而未入库的新名
        映射到库内 canonical 名，供 sketch / final .thy 回写引理引用。
        """
        from ..lemma_proving.usage import lemma_still_sorry
        from .definition_store import DefinitionStore

        path = ProvenLemmaStore.ensure_global(output_dir, domain)
        if (definitions_block or "").strip():
            DefinitionStore.merge_definitions_block(
                output_dir,
                domain,
                definitions_block,
                source_theorem=source_theorem,
            )
        existing_text = path.read_text(encoding="utf-8")
        existing = extract_decl_blocks(existing_text)
        # 论文 2.4.1/2.4.2：已证引理矢量存储（按数据结构分别建库）
        from ..lemma.lemma_vector_store import LemmaVectorStore as _VecStore

        vector_store = _VecStore(
            output_dir, f"proven_embeddings_{normalize_domain(domain)}"
        )
        vector_store.sync(existing)
        strict_index, alpha_index = build_lemma_merge_proposition_index(existing)
        batch_strict: dict[str, str] = dict(strict_index)
        batch_alpha: dict[str, str] = dict(alpha_index)
        alias_map: dict[str, str] = {}
        updated = 0

        same_name_updates: List[tuple[str, str]] = []
        semantic_dupes: List[tuple[str, str, str]] = []
        pending_add: List[tuple[str, str]] = []

        for block in new_blocks:
            text = (block or "").strip()
            if not text:
                continue
            name = extract_fact_name(text)
            if not name:
                continue
            if name in existing:
                same_name_updates.append((name, text))
                continue

            canonical = find_semantic_duplicate_name(
                text,
                strict_index=batch_strict,
                alpha_index=batch_alpha,
            )
            if not canonical:
                is_dup, vec_name, sim = vector_store.is_duplicate(
                    text, threshold=similarity_threshold
                )
                if is_dup and vec_name:
                    canonical = vec_name
                    logger.info(
                        "矢量判重跳过语义重复引理 %s（与库内 %s 余弦相似度 %.4f >= %s）",
                        name,
                        vec_name,
                        sim,
                        similarity_threshold,
                    )
            if canonical:
                alias_map[name] = canonical
                semantic_dupes.append((name, canonical, text))
                logger.info(
                    "合并跳过语义重复引理 %s（与库内 %s 同命题，保留库内名称）",
                    name,
                    canonical,
                )
                continue

            pending_add.append((name, text))
            prop = extract_proposition_key(text)
            if prop:
                batch_strict.setdefault(prop, name)
                batch_alpha.setdefault(
                    alpha_key_for_lemma_block(text), name
                )

        if local_lemma_names:
            # 同批引理互相引用时，若被引用者仍是 sorry（未入库），
            # 只入库引用方会写坏整个领域库；此处按依赖闭包剪枝，双方都留在 unproven。
            from ..lemma_proving.iterator import _lemma_refs_in_block

            local_names = {n for n in local_lemma_names if n}
            pruned: Dict[str, set[str]] = {}

            def _missing_refs(block: str, available: set[str]) -> set[str]:
                return {
                    ref
                    for ref in _lemma_refs_in_block(block)
                    if ref in local_names and ref not in available
                }

            changed = True
            while changed:
                changed = False
                available = (
                    set(existing)
                    | {n for n, _ in pending_add}
                    | set(alias_map)
                    | set(alias_map.values())
                )
                kept: List[tuple[str, str]] = []
                for name, text in pending_add:
                    missing = _missing_refs(text, available)
                    if missing:
                        pruned[name] = missing
                        changed = True
                        continue
                    kept.append((name, text))
                pending_add = kept
            same_name_updates = [
                (n, b)
                for n, b in same_name_updates
                if not _missing_refs(b, available)
            ]
            semantic_dupes = [
                d for d in semantic_dupes if not _missing_refs(d[2], available)
            ]
            for name, missing in sorted(pruned.items()):
                logger.warning(
                    "合并跳过引理 %s：依赖的同批引理未入库 %s（保留在 unproven，避免写坏领域库）",
                    name,
                    ", ".join(sorted(missing)),
                )

        for name, text in same_name_updates:
            old = existing[name]
            if lemma_still_sorry(old) and not lemma_still_sorry(text):
                existing[name] = rewrite_lemma_ref_names(text, alias_map)
                updated += 1

        for _name, canonical, text in semantic_dupes:
            if canonical not in existing:
                continue
            old = existing[canonical]
            if lemma_still_sorry(old) and not lemma_still_sorry(text):
                merged = rewrite_lemma_ref_names(text, alias_map)
                existing[canonical] = retarget_lemma_block_name(
                    merged, canonical
                )
                updated += 1

        for name, text in pending_add:
            rewritten = rewrite_lemma_ref_names(text, alias_map)
            existing[name] = rewritten
            vector_store.add(name, rewritten)
            updated += 1
        if updated:
            vector_store.save()

        all_lemma_blocks: List[str] = []
        for block in existing.values():
            first = (block or "").strip().splitlines()[0] if block else ""
            if _LEMMA_HEAD_LINE.match(first):
                all_lemma_blocks.append(block)
        defs_source = DefinitionStore.read_definitions(output_dir, domain)
        if (definitions_block or "").strip():
            defs_source = ProvenLemmaStore.merge_definition_preambles(
                defs_source, definitions_block
            )
        defs_changed = DefinitionStore.ensure_definitions_for_lemma_blocks(
            output_dir, domain, all_lemma_blocks, source_preamble=defs_source
        )

        # 论文 2.4.1：已证引理保存唯一且递增的数值标识符（证明先后顺序）
        identifiers = ProvenLemmaStore.assign_lemma_identifiers(
            output_dir, domain, list(existing.keys())
        )
        insertion_lemma_order = [
            n
            for n in sorted(
                existing, key=lambda x: identifiers.get(x, 1 << 30)
            )
            if _LEMMA_HEAD_LINE.match(
                ((existing[n] or "").strip().splitlines() or [""])[0]
            )
        ]
        lemma_order = topological_sort_lemma_block_names(
            existing, prefer_order=insertion_lemma_order
        )
        order_changed = lemma_order != insertion_lemma_order
        ordered_blocks = [existing[n] for n in lemma_order]

        if updated or defs_changed or order_changed:
            ProvenLemmaStore.write_proven_thy(
                path,
                ordered_blocks,
            )
            logger.info(
                "全局已证引理库更新 %d 条引理（theorem=%s，合计 %d 条）",
                updated,
                source_theorem or "?",
                len(existing),
            )

        # 每次 merge 后都重算质量分（即使引理数未变，U(i) 也可能变化）
        ProvenLemmaStore.compute_and_save_quality_scores(
            output_dir,
            domain,
            syntax_results=syntax_results,
            proof_difficulty_results=proof_difficulty_results,
            reuse_counts=reuse_counts,
        )
        if alias_map:
            logger.info(
                "合并引理别名映射 %d 条（供 sketch/final 回写）: %s",
                len(alias_map),
                ", ".join(f"{k}->{v}" for k, v in sorted(alias_map.items())),
            )
        return updated, alias_map

    @staticmethod
    def remove_lemma_blocks_from_thy(
        thy_path: Path,
        lemma_names: Sequence[str],
    ) -> None:
        """从 unproven .thy 中删除已迁入全局库的引理块（保留定义与其它引理）。"""
        if not thy_path.is_file() or not lemma_names:
            return
        lines = thy_path.read_text(encoding="utf-8").splitlines()
        to_remove = set(lemma_names)
        out: List[str] = []
        i = 0
        while i < len(lines):
            m = _LEMMA_HEAD_LINE.match(lines[i])
            if m and m.group(3) in to_remove:
                i += 1
                while i < len(lines):
                    if _LEMMA_HEAD_LINE.match(lines[i]) or lines[i].strip() == "end":
                        break
                    i += 1
                while out and not out[-1].strip():
                    out.pop()
                continue
            out.append(lines[i])
            i += 1
        thy_path.write_text("\n".join(out).rstrip() + "\n", encoding="utf-8")
        ProvenLemmaStore.normalize_thy_file(thy_path)
