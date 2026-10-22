"""
维度 2b：证明推导难度评分（used_lemma_count）。

统计证明中显式引用的库引理个数（去重、按出现顺序）。
该数值即引理质量评估中的「证明推导难度」评分。
"""

from __future__ import annotations

import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from ..syntax_complexity import normalize_statement_block
from ...utils.lemma_dedup import extract_fact_name
from .analyzer import count_used_lemmas
from .thy_extract import load_decl_blocks_from_thy, pick_scoring_text

logger = logging.getLogger(__name__)


class ProofDifficultyV2Scorer:
    """对引理/证明文本统计 used_lemma_count（证明推导难度评分）。"""

    def score_statement(
        self, statement: str
    ) -> Tuple[int, List[str], str]:
        """
        返回 (used_lemma_count, used_lemmas, error)。
        """
        text = (statement or "").strip()
        if not text:
            return 0, [], ""
        count, names = count_used_lemmas(text)
        return count, names, ""

    def score_statement_with_context(
        self,
        statement: str,
        *,
        lemma_name: str = "",
        thy_blocks: Optional[Dict[str, str]] = None,
    ) -> Tuple[int, List[str], str]:
        """优先使用 thy 中同名声明的完整证明块再统计。"""
        blocks = thy_blocks or {}
        name = lemma_name or extract_fact_name(statement) or ""
        text = pick_scoring_text(statement, blocks, name)
        return self.score_statement(text)

    def score_statements_batch(
        self,
        items: List[Tuple[str, str]],
        *,
        thy_blocks: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Tuple[int, List[str], str]]:
        """
        items: [(item_id, statement), ...]
        返回 item_id -> (count, used_lemmas, error)
        """
        out: Dict[str, Tuple[int, List[str], str]] = {}
        blocks = thy_blocks or {}
        for item_id, statement in items:
            logger.info("证明推导难度评分（引理使用计数） %s", item_id)
            name, _, _, _ = normalize_statement_block(statement)
            if not name:
                name = extract_fact_name(statement) or ""
            out[item_id] = self.score_statement_with_context(
                statement,
                lemma_name=name,
                thy_blocks=blocks,
            )
        return out

    @staticmethod
    def score_theory_file(thy_path: Path) -> Tuple[int, List[str], str]:
        """统计整个 .thy 中所有证明的引理使用（合并去重按出现顺序）。"""
        if not thy_path.is_file():
            return 0, [], f"文件不存在: {thy_path}"
        text = thy_path.read_text(encoding="utf-8")
        count, names = count_used_lemmas(text)
        return count, names, ""

    @staticmethod
    def score_decl_in_thy(
        thy_path: Path,
        decl_name: str,
    ) -> Tuple[int, List[str], str]:
        """统计 thy 中单个 lemma/theorem 声明块的引理使用。"""
        blocks = load_decl_blocks_from_thy(thy_path)
        block = blocks.get(decl_name)
        if not block:
            return 0, [], f"thy 中未找到声明: {decl_name}"
        count, names = count_used_lemmas(block)
        return count, names, ""
