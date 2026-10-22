"""
单次定理证明运行的落盘上下文（构造引理 + 草图阶段输入与输出）。
"""

from __future__ import annotations

import json
import logging
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

logger = logging.getLogger(__name__)

FN_COMBINED_CONTEXT = "theorem_context.txt"
LEGACY_TEXT_FILES: Tuple[str, ...] = (
    "function_definitions.txt",
    "theorem_statement.txt",
    "informal_proof.txt",
    "lemmas_for_sketch.txt",
    "proof_sketch.txt",
)

_COMBINED_MARKERS: Tuple[Tuple[str, str], ...] = (
    ("function_definitions", "<<<FUNCTION_DEFINITION>>>"),
    ("theorem_statement", "<<<THEOREM_STATEMENT>>>"),
    ("informal_proof", "<<<INFORMAL_PROOF>>>"),
    ("lemmas", "<<<LEMMAS>>>"),
    ("proof_sketch", "<<<PROOF_SKETCH>>>"),
)


class TheoremRunArtifact:
    """写入 {output_dir}/theorem_run/{theorem_name}/ 下的 run_context.json 与草图用文本块。"""

    def __init__(self, output_dir: str, theorem_name: str):
        self._dir = Path(output_dir) / "theorem_run" / theorem_name
        self._path = self._dir / "run_context.json"
        self.theorem_name = theorem_name

    @property
    def dir_path(self) -> Path:
        return self._dir

    def _write_text(self, name: str, content: str) -> None:
        self._dir.mkdir(parents=True, exist_ok=True)
        p = self._dir / name
        with open(p, "w", encoding="utf-8") as f:
            f.write(content or "")
        print(f"[artifact] 已写入 {p}")

    def _build_combined_text(self, data: Dict[str, Any]) -> str:
        values: Dict[str, str] = {
            "function_definitions": data.get("function_definitions_block") or "",
            "theorem_statement": data.get("theorem_statement_block") or "",
            "informal_proof": data.get("informal_proof") or "",
            "lemmas": data.get("lemmas_for_sketch_block") or "",
            "proof_sketch": data.get("latest_sketch") or "",
        }
        parts: List[str] = []
        for key, marker in _COMBINED_MARKERS:
            block = str(values.get(key) or "").rstrip()
            parts.append(marker)
            parts.append(block)
            parts.append("")
        return "\n".join(parts).rstrip() + "\n"

    def _write_combined_text(self, data: Dict[str, Any]) -> None:
        self._write_text(FN_COMBINED_CONTEXT, self._build_combined_text(data))
        self._delete_legacy_text_files()

    def _delete_legacy_text_files(self) -> None:
        for name in LEGACY_TEXT_FILES:
            p = self._dir / name
            if not p.exists():
                continue
            try:
                p.unlink()
                print(f"[artifact] 已删除旧文件 {p}")
            except OSError as e:
                logger.warning("删除旧分文件失败 %s: %s", p, e)

    def _parse_combined_text(self, text: str) -> Optional[Dict[str, str]]:
        positions: List[Tuple[str, int]] = []
        for key, marker in _COMBINED_MARKERS:
            idx = text.find(marker)
            if idx < 0:
                logger.warning("汇总文本缺少段落标记: %s", marker)
                return None
            positions.append((key, idx))
        positions.sort(key=lambda x: x[1])

        out: Dict[str, str] = {}
        for i, (key, start_idx) in enumerate(positions):
            marker = dict(_COMBINED_MARKERS)[key]
            start = start_idx + len(marker)
            end = positions[i + 1][1] if i + 1 < len(positions) else len(text)
            out[key] = text[start:end].strip()
        return {
            "function_definitions": out.get("function_definitions", ""),
            "theorem_statement": out.get("theorem_statement", ""),
            "informal_proof": out.get("informal_proof", ""),
            "lemmas": out.get("lemmas", ""),
            "proof_sketch": out.get("proof_sketch", ""),
        }

    @property
    def json_path(self) -> Path:
        return self._path

    def _load(self) -> Dict[str, Any]:
        if self._path.is_file():
            try:
                with open(self._path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except (json.JSONDecodeError, OSError) as e:
                logger.warning("读取 run_context.json 失败，将覆盖写入: %s", e)
        return {"theorem_name": self.theorem_name}

    def _save(self, data: Dict[str, Any]) -> None:
        self._dir.mkdir(parents=True, exist_ok=True)
        tmp = self._path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        tmp.replace(self._path)
        print(f"[artifact] 已更新 {self._path}")

    def write_after_construct(
        self,
        function_definitions_block: str,
        theorem_statement_block: str,
        informal_proof: str,
        constructed_lemma_concepts: Optional[List[Dict[str, str]]],
        construct_lemma_raw: str,
        error: Optional[str] = None,
    ) -> None:
        data = self._load()
        data.update(
            {
                "theorem_name": self.theorem_name,
                "function_definitions_block": function_definitions_block,
                "theorem_statement_block": theorem_statement_block,
                "informal_proof": informal_proof or "",
                "constructed_lemma_concepts": constructed_lemma_concepts or [],
                "construct_lemma_raw": construct_lemma_raw or "",
                "construct_lemma_error": error,
                "merged_lemma_concepts": data.get("merged_lemma_concepts"),
                "sketches": data.get("sketches") or [],
                "updated_construct_at": datetime.now(timezone.utc).isoformat(),
            }
        )
        self._save(data)
        self._write_combined_text(data)

    def update_merged_lemma_concepts(
        self,
        merged: List[Dict[str, str]],
        lemmas_for_sketch_block: str,
    ) -> None:
        data = self._load()
        data["merged_lemma_concepts"] = merged
        data["lemmas_for_sketch_block"] = lemmas_for_sketch_block or ""
        data["updated_merged_at"] = datetime.now(timezone.utc).isoformat()
        self._save(data)
        self._write_combined_text(data)

    def read_sketch_prompt_blocks(self) -> Optional[Dict[str, str]]:
        """第二次请求草图前：从汇总文本读取四项输入块。"""
        combined = self._dir / FN_COMBINED_CONTEXT
        if combined.is_file():
            try:
                parsed = self._parse_combined_text(combined.read_text(encoding="utf-8"))
                if parsed is not None:
                    return {
                        "function_definitions": parsed.get("function_definitions", ""),
                        "theorem_statement": parsed.get("theorem_statement", ""),
                        "informal_proof": parsed.get("informal_proof", ""),
                        "lemmas": parsed.get("lemmas", ""),
                    }
            except OSError as e:
                logger.warning("读取汇总文本失败 %s: %s", combined, e)
        logger.warning("草图汇总文本缺失，将回退内存块: %s", combined)
        return None

    def append_sketch(self, iteration: int, sketch: str) -> None:
        data = self._load()
        sketches = data.get("sketches") or []
        sketches.append(
            {
                "iteration": iteration,
                "sketch": sketch,
                "saved_at": datetime.now(timezone.utc).isoformat(),
            }
        )
        data["sketches"] = sketches
        data["latest_sketch"] = sketch
        data["latest_sketch_iteration"] = iteration
        data["updated_sketch_at"] = datetime.now(timezone.utc).isoformat()
        self._save(data)
        self._write_combined_text(data)
