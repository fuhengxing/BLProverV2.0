"""
引理迭代证明模块（主定理通过后，证明 unproven 中全部 sorry 引理）。

目录结构：
  usage.py              — 分析主定理引用了哪些引理
  iterator.py           — 单条引理 LLM 迭代证明
  pipeline.py           — 编排入口
  lemma_proof_prompt.txt — 首次证明
  lemma_proof_repair_prompt.txt — Isabelle 失败后修复
"""

from .iterator import (
    LemmaProofIterator,
    default_lemma_proof_prompt_path,
    default_lemma_proof_repair_prompt_path,
    load_lemma_proof_prompt,
    load_lemma_proof_repair_prompt,
    split_lemma_proof_prompt_file,
)
from .pipeline import UsedLemmaProofResult, prove_used_lemmas_after_theorem
from .usage import (
    LemmaUsageEntry,
    TheoremLemmaUsageReport,
    analyze_theorem_lemma_usage,
    lemma_still_sorry,
)

__all__ = [
    "LemmaProofIterator",
    "LemmaUsageEntry",
    "TheoremLemmaUsageReport",
    "UsedLemmaProofResult",
    "analyze_theorem_lemma_usage",
    "default_lemma_proof_prompt_path",
    "default_lemma_proof_repair_prompt_path",
    "load_lemma_proof_prompt",
    "load_lemma_proof_repair_prompt",
    "split_lemma_proof_prompt_file",
    "lemma_still_sorry",
    "prove_used_lemmas_after_theorem",
]
