"""
未证明引理持久化（构造引理阶段产出），与已验证引理库分 collection 存储。
支持将引理写出为独立 .thy 文件，供主 .thy import 以支持 sledgehammer 跨文件检索。
"""

from __future__ import annotations

import hashlib
import json
import logging
import re
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from .domain import normalize_domain
from .thy_imports import DEFS_THEORY_NAME, theorem_defs_imports
from .lemma import Lemma
from .lemma_cache import chroma_embedding_function_for_config
from .lemma_chroma_storage import LemmaChromaStorage

logger = logging.getLogger(__name__)

_LEMMA_HEAD_RE = re.compile(
    r"^\s*(lemma|theorem|corollary)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE,
)
_LEMMA_ONLY_KIND_RE = re.compile(
    r"^\s*(lemma|corollary|proposition)\s+",
    re.IGNORECASE,
)
_IMPORTS_LINE_RE = re.compile(r"^imports\s+(.+)$", re.IGNORECASE | re.MULTILINE)

_FIXES_CLAUSE_RE = re.compile(
    r"\bfixes\b(.*?)(?=\b(?:assumes|shows|obtains|proof|qed|sorry|note)\b|\Z)",
    re.DOTALL,
)
_COMPOSITE_TYPE_HINT_RE = re.compile(r"[\s,\u00d7\u21d2\u2192]")

_PROOF_BODY_LINE_RE = re.compile(
    r"^\s*(?:proof|by|apply|done|qed|using|unfolding|hence|thus|have|show|"
    r"obtain|from|with|then|moreover|ultimately|also|finally|let|case|next|"
    r"note|fix|assume|presume|define|consider|guess|interpret|supply)\b"
)


def _quote_one_fixes_binding(binding: str) -> str:
    """Quote a composite type inside one ``name :: type`` binding."""
    if "::" not in binding:
        return binding
    name, sep, typ = binding.partition("::")
    stripped = typ.strip()
    if not stripped:
        return binding
    if stripped.startswith('"') and stripped.endswith('"'):
        return binding
    if not _COMPOSITE_TYPE_HINT_RE.search(stripped):
        return binding
    lead = typ[: len(typ) - len(typ.lstrip())]
    trail = typ[len(typ.rstrip()) :]
    return f'{name}{sep}{lead}"{stripped}"{trail}'


def strip_lemma_proof_body(text: str) -> str:
    """Cut a proof body that was pasted into a lemma declaration.

    The unproven theory keeps plain statements plus ``sorry``; when an LLM
    returns ``lemma X: "P" by simp`` or a full ``proof ... qed`` block as the
    candidate statement, keeping the body makes the appended ``sorry`` an
    error ("Bad context for command sorry"). Only the declaration is kept.
    """
    if not text:
        return text
    lines = text.split("\n")
    kept: List[str] = []
    for idx, line in enumerate(lines):
        if idx > 0 and _PROOF_BODY_LINE_RE.match(line):
            break
        kept.append(line)
    out: List[str] = []
    for line in "\n".join(kept).split("\n"):
        if "(*" not in line:
            m = re.search(r"\bshows\b", line)
            if m:
                tail = line[m.end():]
                cut: Optional[int] = None
                for kw in (" by ", " proof ", " apply "):
                    pos = tail.find(kw)
                    while pos >= 0:
                        if tail[:pos].count(chr(34)) % 2 == 0:
                            cut = pos if cut is None else min(cut, pos)
                            break
                        pos = tail.find(kw, pos + 1)
                if cut is not None:
                    line = line[: m.end() + cut]
        out.append(line)
    return "\n".join(out).rstrip()


def quote_composite_fixes_types(text: str) -> str:
    """Quote composite types in Isabelle ``fixes`` clauses.

    Isabelle requires composite types such as ``fixes s :: "\u0027a stack"``
    to be double quoted, while bare type variables (``fixes v :: \u0027a``)
    and simple type names (``fixes n :: nat``) must stay unquoted.
    """
    if not text or "fixes" not in text:
        return text

    def _repl(match: "re.Match[str]") -> str:
        parts = re.split(r"(\s+and\s+)", match.group(1))
        rewritten = [
            part
            if re.fullmatch(r"\s+and\s+", part or "")
            else _quote_one_fixes_binding(part)
            for part in parts
        ]
        return "fixes" + "".join(rewritten)

    return _FIXES_CLAUSE_RE.sub(_repl, text)


class UnprovenLemmaStore:
    """可选：Chroma 独立 collection 存储未证明引理陈述；.thy 写入与 Chroma 无关。"""

    def __init__(self, config: Optional["LemmaCacheConfig"] = None):
        if config is None:
            from ..config import LemmaCacheConfig as _LemmaCacheConfig

            config = _LemmaCacheConfig()
        self.config = config
        self._storage: Optional[LemmaChromaStorage] = None
        if self.config.chroma_enabled:
            embedding_fn = chroma_embedding_function_for_config(self.config)
            self._storage = LemmaChromaStorage(
                chroma_path=self.config.chroma_path,
                collection_name=self.config.unproven_collection,
                embedding_function=embedding_fn,
            )
        else:
            logger.info(
                "ChromaDB 未证引理库已禁用（chroma_enabled=False）；"
                "不读写 %s（collection=%s）",
                self.config.chroma_path,
                self.config.unproven_collection,
            )

    @staticmethod
    def _local_vector_dir(output_dir: str | Path) -> Path:
        return Path(output_dir) / "results" / "proven_lemmas"

    @staticmethod
    def _local_metadata_path(output_dir: str | Path, domain: str) -> Path:
        return UnprovenLemmaStore._local_vector_dir(output_dir) / (
            f"unproven_lemmas_index_{normalize_domain(domain or 'unknown')}.json"
        )

    @staticmethod
    def _statement_name(text: str, index: int) -> str:
        from ..utils.lemma_dedup import extract_fact_name

        name = extract_fact_name(text) or ""
        if name:
            return name
        digest = hashlib.sha1((text or "").encode("utf-8")).hexdigest()[:12]
        return f"unproven_{digest}_{index}"

    def _upsert_local_vectors(
        self,
        texts: List[str],
        theorem_name: str,
        *,
        domain: str,
        stage: str,
        output_dir: str | Path,
    ) -> int:
        """论文 2.4.1：未证明引理的本地矢量库 + 元数据（零外部依赖）。"""
        from .lemma_vector_store import LemmaVectorStore

        stem = f"unproven_embeddings_{normalize_domain(domain or 'unknown')}"
        store = LemmaVectorStore(output_dir, stem)
        meta_path = self._local_metadata_path(output_dir, domain)
        meta: dict = {}
        if meta_path.is_file():
            try:
                loaded = json.loads(meta_path.read_text(encoding="utf-8"))
                if isinstance(loaded, dict):
                    meta = loaded
            except Exception:
                meta = {}
        lemmas = meta.get("lemmas")
        if not isinstance(lemmas, dict):
            lemmas = {}
        next_id = max(
            [int(v.get("id") or 0) for v in lemmas.values() if isinstance(v, dict)]
            or [0]
        ) + 1
        added = 0
        threshold = float(
            getattr(self.config, "similarity_threshold", 0.92) or 0.92
        )
        known_names = set(store.names())
        for idx, text in enumerate(texts):
            name = self._statement_name(text, idx)
            entry = dict(lemmas.get(name) or {})
            if "id" not in entry:
                entry["id"] = next_id
                next_id += 1
            # 论文 2.4.2：未证库同样做余弦判重。判重只做标记，不丢弃生成记录
            # （用户要求保留全部候选引理用于后续对比）。
            is_dup, dup_name, sim = (
                (False, None, 0.0)
                if name in known_names
                else store.is_duplicate(text, threshold=threshold)
            )
            if is_dup and dup_name and dup_name != name:
                entry["duplicate_of"] = dup_name
                entry["similarity"] = round(float(sim), 4)
            else:
                entry.pop("duplicate_of", None)
                entry.pop("similarity", None)
                store.add(name, text)
                known_names.add(name)
            entry.update(
                {
                    "statement": text,
                    "domain": normalize_domain(domain or "unknown"),
                    "stage": stage or "",
                    "theorem_name": theorem_name or "",
                }
            )
            lemmas[name] = entry
            added += 1
        store.save()
        meta_path.parent.mkdir(parents=True, exist_ok=True)
        meta_path.write_text(
            json.dumps(
                {
                    "domain": normalize_domain(domain or "unknown"),
                    "lemmas": lemmas,
                },
                ensure_ascii=False,
                indent=2,
            )
            + "\n",
            encoding="utf-8",
            newline="\n",
        )
        logger.info(
            "未证明引理本地矢量库写入 %d 条（path=%s）",
            added,
            store.path,
        )
        return added

    def upsert_from_construct(
        self,
        statements: List[str],
        theorem_name: str,
        *,
        domain: str = "",
        stage: str = "",
        output_dir: Optional[str | Path] = None,
    ) -> int:
        """
        将本轮构造的引理写入未证明库（upsert，与已验证 lemmas collection 分离）。

        - output_dir 提供时，始终写入本地矢量库 + 元数据（论文 2.4.1 双库之一）。
        - chroma_enabled=True 时额外写入 Chroma collection；关闭时不触碰磁盘。
        """
        texts = [(stmt or "").strip() for stmt in statements]
        texts = [text for text in texts if text]
        n = 0
        if output_dir and texts:
            n += self._upsert_local_vectors(
                texts,
                theorem_name,
                domain=domain,
                stage=stage,
                output_dir=output_dir,
            )
        if not self._storage:
            return n
        for text in texts:
            lemma = Lemma(
                statement=text,
                proof="",
                status="unverified",
                metadata={
                    "source": "construct_lemma",
                    "theorem_name": theorem_name,
                    "domain": domain or "",
                    "stage": stage or "",
                },
            )
            self._storage.upsert_lemma(lemma)
            n += 1
        if texts:
            logger.info(
                "未证明引理库写入 %d 条（collection=%s, theorem=%s）",
                len(texts),
                self.config.unproven_collection,
                theorem_name,
            )
        return n

    @staticmethod
    def read_defs_preamble_for_lemma_thy(defs_thy_path: Path) -> str:
        """从 domain defs.thy 读取函数定义块，供引理证明 LLM prompt 使用。"""
        path = Path(defs_thy_path)
        if not path.is_file():
            logger.warning("defs.thy 不存在，引理证明 prompt 无函数定义: %s", path)
            return ""
        from .proven_lemma_store import ProvenLemmaStore

        return ProvenLemmaStore.extract_definitions_preamble(
            path.read_text(encoding="utf-8")
        )

    @staticmethod
    def format_definitions_block(
        theorem_data: Optional[dict] = None,
        *,
        other_formal: str = "",
        function_definitions: Optional[Dict[str, str]] = None,
        function_names: Optional[Sequence[str]] = None,
        other_rules: Optional[Sequence[str]] = None,
    ) -> str:
        """从定理 JSON 组装 type_synonym / definition / primrec 等定义块。"""
        from ..sketch.construct_lemma_generator import ordered_function_definition_items

        parts: List[str] = []
        data = theorem_data or {}
        other = (other_formal or data.get("other formal") or "").strip()
        if other:
            parts.append(other)
        func_defs = function_definitions
        if func_defs is None:
            func_defs = data.get("formal function definitions", {}) or {}
        names = function_names
        if names is None:
            names = data.get("function names")
        for _name, defn in ordered_function_definition_items(func_defs, names):
            text = (defn or "").strip()
            if text:
                parts.append(text)
        rules = other_rules
        if rules is None:
            rules = data.get("other rules") or []
        for rule in rules:
            parts.append(f"(* Using rule: {rule} *)")
        return "\n\n".join(parts).strip()

    @staticmethod
    def write_unproven_lemma_thy(
        output_path: Path,
        lemma_statements: List[str],
        theory_name: str,
        *,
        packages: str = "Main",
        quick_and_dirty: bool = True,
        theorem_data: Optional[dict] = None,
        definitions_block: str = "",
        domain: str = "",
    ) -> None:
        """
        将引理列表组装为独立 .thy 文件（默认不含定义块；定义在同领域 defs.thy）。
        """
        defs = (definitions_block or "").strip()

        pkgs = (packages or "Main").strip()
        if domain and "../" not in pkgs:
            base = pkgs.split()[0] if pkgs else "Main"
            from .thy_imports import theorem_unproven_imports

            pkgs = theorem_unproven_imports(packages=base, domain=domain)
        elif "../" not in pkgs and f"/{DEFS_THEORY_NAME}" not in pkgs:
            raise ValueError(
                "write_unproven_lemma_thy 需要 domain 参数以生成 ../<domain>/defs import"
            )

        content = f"""theory "{theory_name}"
imports {pkgs}
begin

declare [[quick_and_dirty = {str(quick_and_dirty).lower()}]]

"""
        if defs:
            content += f"{defs}\n\n"

        for stmt in lemma_statements:
            text = quote_composite_fixes_types(
                strip_lemma_proof_body((stmt or "").strip())
            )
            if not text:
                continue
            content += f"{text}\n\n"

        content += "end\n"
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(content, encoding="utf-8")
        from .proven_lemma_store import ProvenLemmaStore

        ProvenLemmaStore.normalize_thy_file(output_path)
        logger.info(
            "引理 .thy 已写入: %s（定义=%s，引理 %d 条）",
            output_path,
            "有" if defs else "无",
            len(lemma_statements),
        )

    @staticmethod
    def parse_extra_lemma_blocks(extra_lemmas: str) -> Dict[str, str]:
        """从草图修复 JSON 的 extra_lemmas 字段解析引理块（仅 lemma/corollary/proposition）。"""
        from ..eval.proof_difficulty_score_v2.thy_extract import extract_decl_blocks

        text = (extra_lemmas or "").strip()
        if not text:
            return {}
        wrapped = (
            f'theory "_parse_extra"\nimports Main\nbegin\n\n{text}\n\nend\n'
        )
        blocks: Dict[str, str] = {}
        for name, block in extract_decl_blocks(wrapped).items():
            if _LEMMA_ONLY_KIND_RE.match(block):
                blocks[name] = block
            else:
                logger.warning(
                    "extra_lemmas 跳过非引理声明: %s", name
                )
        return blocks

    @staticmethod
    def merge_extra_lemmas_into_unproven_thy(
        unproven_path: Path,
        extra_lemmas: str,
        theory_name: str,
        *,
        packages: str = "Main",
        theorem_data: Optional[dict] = None,
        domain: str = "",
    ) -> List[str]:
        """
        将草图修复返回的 extra_lemmas 并入 unproven_lemmas.thy。
        同名引理以本次 extra 为准；保留已有定义块与 imports。
        返回本次新增或更新的引理名列表。
        """
        from ..eval.proof_difficulty_score_v2.thy_extract import extract_decl_blocks

        extra_blocks = UnprovenLemmaStore.parse_extra_lemma_blocks(extra_lemmas)
        if not extra_blocks:
            return []

        existing_blocks: Dict[str, str] = {}
        pkgs = packages or theorem_defs_imports()

        if unproven_path.is_file():
            text = unproven_path.read_text(encoding="utf-8")
            for name, block in extract_decl_blocks(text).items():
                if _LEMMA_ONLY_KIND_RE.match(block):
                    existing_blocks[name] = block
            m = _IMPORTS_LINE_RE.search(text)
            if m:
                pkgs = m.group(1).strip()

        order = list(existing_blocks.keys())
        updated: List[str] = []
        for name, block in extra_blocks.items():
            existing_blocks[name] = block
            if name not in order:
                order.append(name)
            updated.append(name)

        statements = [existing_blocks[n] for n in order]
        UnprovenLemmaStore.write_unproven_lemma_thy(
            unproven_path,
            statements,
            theory_name,
            packages=pkgs,
            definitions_block="",
            domain=domain,
        )
        logger.info(
            "草图修复 extra_lemmas 已并入 %s（%d 条: %s）",
            unproven_path,
            len(updated),
            ", ".join(updated),
        )
        return updated
