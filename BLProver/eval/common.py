"""引理质量评估 — 阶段常量与构造引理列表工具。"""

from __future__ import annotations

from typing import List

from .syntax_complexity import BatchAnalysisItem

STAGE_STEP1 = "step1_construct_lemmas1"
STAGE_STEP3 = "step3_construct_lemmas2"
STAGE_PROVEN_LIBRARY = "proven_lemma_library"
STAGE_PROVEN_LIBRARY_LABEL = "已证引理库 (proven_lemma_library)"


def build_batch_items(statements: List[str], stage: str) -> List[BatchAnalysisItem]:
    items: List[BatchAnalysisItem] = []
    for idx, stmt in enumerate(statements, start=1):
        text = (stmt or "").strip()
        if not text:
            continue
        items.append(
            BatchAnalysisItem(
                item_id=f"{stage}#{idx}",
                statement=text,
                inline_name=f"__eval_s_{stage}_{idx}",
            )
        )
    return items
