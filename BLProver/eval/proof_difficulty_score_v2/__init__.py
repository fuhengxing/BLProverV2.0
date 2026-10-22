"""
维度 2b：证明推导难度（引理使用计数，去重、按出现顺序）。

统计证明文本中 via using / simp add / metis 等显式引用的库引理名个数。
与 proof_difficulty_score（LLM）独立，互不修改。
"""

from .analyzer import (
    count_used_lemmas,
    count_used_lemmas_in_text,
    extract_proof_region,
    extract_used_lemma_names,
    parse_decl_name,
)
from .scorer import ProofDifficultyV2Scorer
from .thy_extract import (
    load_decl_blocks_from_thy,
    merge_decl_blocks_from_thy_files,
    pick_scoring_text,
)

__all__ = [
    "count_used_lemmas",
    "count_used_lemmas_in_text",
    "extract_proof_region",
    "extract_used_lemma_names",
    "parse_decl_name",
    "ProofDifficultyV2Scorer",
    "load_decl_blocks_from_thy",
    "merge_decl_blocks_from_thy_files",
    "pick_scoring_text",
]
