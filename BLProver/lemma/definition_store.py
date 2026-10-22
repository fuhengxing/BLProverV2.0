"""
按领域存放函数定义：output/theory/<domain>/defs.thy（imports Main）。
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Optional, Sequence

from .domain import get_domain_group, normalize_domain
from .proven_lemma_store import ProvenLemmaStore
from .thy_imports import DEFS_THEORY_NAME, PROVEN_THEORY_NAME, domain_defs_thy_imports
from .unproven_lemma_store import UnprovenLemmaStore

logger = logging.getLogger(__name__)


class DefinitionStore:
    """跨定理、按 domain 共享的形式化定义 .thy 读写与合并。"""

    @staticmethod
    def domain_dir(output_dir: str | Path, domain: str) -> Path:
        d = normalize_domain(domain)
        group = get_domain_group(d)
        if group:
            return Path(output_dir) / "theory" / group / d
        return Path(output_dir) / "theory" / d

    @staticmethod
    def defs_thy_path(output_dir: str | Path, domain: str) -> Path:
        return DefinitionStore.domain_dir(output_dir, domain) / f"{DEFS_THEORY_NAME}.thy"

    @staticmethod
    def _extract_defs_body(thy_text: str) -> str:
        """Return everything between ``begin`` and ``end`` in defs.thy.

        Unlike ``extract_definitions_preamble`` this does NOT stop at the first
        lemma: background lemmas shipped with a definition block (for example
        the List_Index facts that follow ``last_index``) are part of the domain
        preamble and must survive every merge/rewrite.
        """
        import re as _re

        lines = (thy_text or "").splitlines()
        out = []
        past_begin = False
        for line in lines:
            if _re.match(r"^\s*begin\s*$", line, _re.IGNORECASE):
                past_begin = True
                continue
            if not past_begin:
                continue
            if _re.match(r"^\s*declare\s*\[\[quick_and_dirty", line, _re.IGNORECASE):
                continue
            if line.strip().lower() == "end":
                break
            out.append(line)
        return "\n".join(out).strip()

    @staticmethod
    def read_definitions(output_dir: str | Path, domain: str) -> str:
        path = DefinitionStore.defs_thy_path(output_dir, domain)
        if not path.is_file():
            return ""
        return DefinitionStore._extract_defs_body(path.read_text(encoding="utf-8"))

    @staticmethod
    def write_defs_thy(
        path: Path,
        definitions_block: str,
        *,
        packages: str = "Main",
        quick_and_dirty: bool = False,
    ) -> None:
        defs = ProvenLemmaStore.dedupe_definition_preamble(
            ProvenLemmaStore._strip_stray_end_lines(definitions_block or "")
        )
        defs = ProvenLemmaStore._sanitize_isabelle_symbols(defs)
        defs = ProvenLemmaStore._qualify_shadowed_fun_refs_in_definitions(
            defs, theory_name=DEFS_THEORY_NAME
        )
        content = f'''theory "{DEFS_THEORY_NAME}"
imports {domain_defs_thy_imports(packages=packages)}
begin

'''
        if quick_and_dirty:
            content += f"declare [[quick_and_dirty = {str(quick_and_dirty).lower()}]]\n\n"
        if defs:
            content += f"{defs}\n\n"
        content += "end\n"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        ProvenLemmaStore.normalize_thy_file(path)

    @staticmethod
    def ensure_domain(output_dir: str | Path, domain: str) -> Path:
        path = DefinitionStore.defs_thy_path(output_dir, domain)
        if not path.is_file():
            DefinitionStore.write_defs_thy(path, "")
        return path

    @staticmethod
    def _definition_chunks_by_name(preamble: str) -> dict[str, str]:
        chunks: dict[str, str] = {}
        for chunk in ProvenLemmaStore._split_definition_chunks(preamble or ""):
            text = chunk.strip()
            if not text:
                continue
            names = ProvenLemmaStore._chunk_defining_names(text)
            if names:
                chunks[sorted(names)[0]] = text
        return chunks

    @staticmethod
    def _normalize_definition_text(text: str) -> str:
        import re

        cleaned = re.sub(r"\(\*.*?\*\)", " ", text or "", flags=re.DOTALL)
        return " ".join(cleaned.split())

    @staticmethod
    def _record_definition_conflicts(
        output_dir: str | Path,
        domain: str,
        conflicts: dict[str, dict],
        *,
        source_theorem: str = "",
    ) -> None:
        if not conflicts:
            return
        path = DefinitionStore.defs_thy_path(output_dir, domain).parent / "defs_conflicts.json"
        payload: dict = {}
        if path.is_file():
            try:
                loaded = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(loaded, dict):
                    payload = loaded
            except Exception:
                payload = {}
        for name, info in conflicts.items():
            entry = dict(payload.get(name) or {})
            sources = list(entry.get("sources") or [])
            if source_theorem and source_theorem not in sources:
                sources.append(source_theorem)
            entry.update(
                {
                    "kept": info["kept"],
                    "ignored": info["ignored"],
                    "sources": sources,
                    "policy": "keep_existing",
                }
            )
            payload[name] = entry
        path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        logger.warning(
            "领域 %s defs 存在同名不同内容定义 %d 个，已保留旧定义并记录: %s",
            domain,
            len(conflicts),
            ", ".join(sorted(conflicts)),
        )

    @staticmethod
    def merge_definitions_block(
        output_dir: str | Path,
        domain: str,
        new_block: str,
        *,
        source_theorem: str = "",
        function_names: Optional[Sequence[str]] = None,
    ) -> int:
        """将新定义块合并进 domain defs.thy（只增不减，同名保留旧定义）。"""
        text = (new_block or "").strip()
        if not text:
            return 0
        path = DefinitionStore.ensure_domain(output_dir, domain)
        existing = DefinitionStore.read_definitions(output_dir, domain)
        before_names = ProvenLemmaStore.definition_names_in_preamble(existing)
        existing_chunks = DefinitionStore._definition_chunks_by_name(existing)
        incoming_chunks = DefinitionStore._definition_chunks_by_name(text)
        conflicts: dict[str, dict] = {}
        for name, incoming in incoming_chunks.items():
            kept = existing_chunks.get(name)
            if kept and DefinitionStore._normalize_definition_text(kept) != DefinitionStore._normalize_definition_text(incoming):
                conflicts[name] = {"kept": kept, "ignored": incoming}
        merged = ProvenLemmaStore.merge_definition_preambles(
            existing, text, function_names=function_names
        )
        after_names = ProvenLemmaStore.definition_names_in_preamble(merged)
        added = len(after_names - before_names)
        if merged != existing:
            DefinitionStore.write_defs_thy(path, merged)
            logger.info(
                "领域 %s defs 已更新（theorem=%s，新增定义名 %d 个，现有 %d 个）",
                domain,
                source_theorem or "?",
                added,
                len(after_names),
            )
        DefinitionStore._record_definition_conflicts(
            output_dir, domain, conflicts, source_theorem=source_theorem
        )
        return added

    @staticmethod
    def domain_data_dir(data_dir: str | Path, domain: str) -> Path:
        return Path(data_dir) / normalize_domain(domain)

    @staticmethod
    def merge_from_domain_data(
        output_dir: str | Path,
        domain: str,
        data_dir: str | Path,
        *,
        source_theorem: str = "",
    ) -> int:
        """把 data/<domain>/*.json 的定义全部补进领域 defs.thy。

        单个定理 JSON 往往只声明它自己用到的函数名，可能引用同领域其他数据文件
        才定义的类型/函数（例如 size_increase 引用 capacity）。按领域扫描可避免
        defs.thy 因单条数据缺定义而残缺。
        """
        root = DefinitionStore.domain_data_dir(data_dir, domain)
        if not root.is_dir():
            return 0
        added = 0
        for json_path in sorted(root.glob("*.json")):
            try:
                data = json.loads(json_path.read_text(encoding="utf-8"))
            except Exception as exc:
                logger.warning("跳过无法解析的领域数据文件 %s: %s", json_path, exc)
                continue
            if not isinstance(data, dict):
                continue
            block = UnprovenLemmaStore.format_definitions_block(data)
            if not block.strip():
                continue
            added += DefinitionStore.merge_definitions_block(
                output_dir,
                domain,
                block,
                source_theorem=json_path.stem or source_theorem,
                function_names=data.get("function names"),
            )
        return added

    @staticmethod
    def collect_domain_definitions(
        data_dir: str | Path,
        domain: str,
        *,
        exclude_theorem: str = "",
    ) -> str:
        """汇总 data/<domain>/*.json 的全部定义（同名保留首次出现）。

        提示词需要与领域 defs.thy 看到同一套定义：单个定理 JSON 往往只声明
        自己用到的函数名，可能引用同领域其他数据文件才定义的类型/函数
        （例如 size_increase 的 isfull 依赖 capacity）。
        """
        root = DefinitionStore.domain_data_dir(data_dir, domain)
        if not root.is_dir():
            return ""
        merged = ""
        for json_path in sorted(root.glob("*.json")):
            if exclude_theorem and json_path.stem == exclude_theorem:
                continue
            try:
                data = json.loads(json_path.read_text(encoding="utf-8"))
            except Exception as exc:
                logger.warning("跳过无法解析的领域数据文件 %s: %s", json_path, exc)
                continue
            if not isinstance(data, dict):
                continue
            block = UnprovenLemmaStore.format_definitions_block(data)
            if not block.strip():
                continue
            merged = ProvenLemmaStore.merge_definition_preambles(
                merged,
                block,
                function_names=data.get("function names"),
            )
        return merged

    @staticmethod
    def merge_from_theorem_data(
        output_dir: str | Path,
        domain: str,
        theorem_data: Optional[dict],
        *,
        source_theorem: str = "",
        data_dir: Optional[str | Path] = None,
    ) -> int:
        block = UnprovenLemmaStore.format_definitions_block(theorem_data)
        names = None
        if theorem_data:
            names = theorem_data.get("function names")
        added = DefinitionStore.merge_definitions_block(
            output_dir,
            domain,
            block,
            source_theorem=source_theorem,
            function_names=names,
        )
        if data_dir:
            added += DefinitionStore.merge_from_domain_data(
                output_dir,
                domain,
                data_dir,
                source_theorem=source_theorem,
            )
        return added

    @staticmethod
    def ensure_definitions_for_lemma_blocks(
        output_dir: str | Path,
        domain: str,
        lemma_blocks,
        source_preamble: str = "",
    ) -> bool:
        existing = DefinitionStore.read_definitions(output_dir, domain)
        merged = ProvenLemmaStore.ensure_definitions_for_lemma_blocks(
            existing,
            source_preamble,
            lemma_blocks,
        )
        if merged == existing:
            return False
        DefinitionStore.write_defs_thy(
            DefinitionStore.defs_thy_path(output_dir, domain), merged
        )
        return True

    @staticmethod
    def migrate_legacy_root_defs(output_dir: str | Path) -> bool:
        """将旧版 output/theory/defs.thy 按内容拆入 priority_queue / stack 领域。"""
        root = Path(output_dir) / "theory" / f"{DEFS_THEORY_NAME}.thy"
        if not root.is_file():
            return False
        text = root.read_text(encoding="utf-8")
        preamble = ProvenLemmaStore.extract_definitions_preamble(text)
        if not preamble.strip():
            root.unlink(missing_ok=True)
            return False

        pq_chunks: list[str] = []
        stack_chunks: list[str] = []
        for chunk in ProvenLemmaStore._split_definition_chunks(preamble):
            body = chunk.strip()
            if not body:
                continue
            if "pri_queue" in body or "Abs_pq" in body or "alist_of" in body:
                pq_chunks.append(body)
            elif "stack" in body or body.startswith('definition "emp'):
                stack_chunks.append(body)
            else:
                pq_chunks.append(body)

        if pq_chunks:
            DefinitionStore.merge_definitions_block(
                output_dir,
                "priority_queue",
                "\n\n".join(pq_chunks),
                source_theorem="migration",
            )
        if stack_chunks:
            DefinitionStore.merge_definitions_block(
                output_dir,
                "stack",
                "\n\n".join(stack_chunks),
                source_theorem="migration",
            )
        root.unlink(missing_ok=True)
        logger.info("已迁移旧版根目录 defs.thy 至领域目录")
        return True

    @staticmethod
    def migrate_legacy_proven_split(
        output_dir: str | Path, domain: str = "priority_queue"
    ) -> bool:
        """将旧版 proven 内嵌 definitions 迁到领域 defs，并重写 proven 为仅引理。"""
        theory_root = Path(output_dir) / "theory"
        candidates = [
            theory_root / f"{PROVEN_THEORY_NAME}.thy",
            DefinitionStore.domain_dir(output_dir, domain) / f"{PROVEN_THEORY_NAME}.thy",
        ]
        proven_path = next((p for p in candidates if p.is_file()), None)
        if proven_path is None:
            return False
        text = proven_path.read_text(encoding="utf-8")
        defs_block = ProvenLemmaStore.extract_definitions_preamble(text)
        target_domain = domain
        if proven_path.parent.name != "theory":
            target_domain = proven_path.parent.name
        if defs_block.strip():
            DefinitionStore.merge_definitions_block(
                output_dir, target_domain, defs_block, source_theorem="migration"
            )
        lemma_blocks = ProvenLemmaStore.list_lemma_only_blocks_from_text(text)
        target = ProvenLemmaStore.proven_thy_path(output_dir, target_domain)
        ProvenLemmaStore.write_proven_thy(target, lemma_blocks)
        if proven_path != target and proven_path.is_file():
            proven_path.unlink()
        logger.info("已从 legacy proven 拆分 definitions 到 %s/defs.thy", target_domain)
        return True

    # 兼容旧调用名
    global_thy_path = defs_thy_path
    ensure_global = ensure_domain
