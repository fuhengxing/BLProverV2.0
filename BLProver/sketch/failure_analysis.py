"""
论文 4.3：定理/草图验证失败的根因判定与回溯路由。

失败根因分两类：
- missing_lemma：证明引用了当前上下文中不存在的引理/事实（引理缺失）
  -> 回溯至 2.2.3 修复引理构造策略补引理；
- structure_error：证明草图的逻辑结构/证明步骤错误（其余情况）
  -> 回溯至 2.2.1，修正非形式化证明并重新生成形式化证明草图。

判定以 Isabelle 错误文本的规则匹配为主（确定性、可直接单测）；调用方可在规则无法
判定时再用大模型兜底。
"""

from __future__ import annotations

import re
from typing import Optional, Sequence

STRUCTURE_ERROR = "structure_error"
MISSING_LEMMA = "missing_lemma"

# 引理/事实缺失信号
_MISSING_LEMMA_RE = re.compile(
    r"("
    r"undefined\s+(?:fact|constant|theorem|function|type)"
    r"|unknown\s+(?:fact|constant|theorem|function|type)"
    r"|fact\s+\S+\s+not\s+found"
    r"|no\s+such\s+(?:fact|constant|theorem)"
    r"|undeclared\s+\S+"
    r"|bad\s+name\s+binding"
    r")",
    re.IGNORECASE,
)

# 明确的"结构/证明步骤"错误信号（与引理缺失区分）
# Local proof facts are bound by the proof context, not by the lemma library.
# Referring to them outside their scope is a proof-step error, not a missing lemma.
_LOCAL_FACT_RE = re.compile(
    r'undefined\s+fact:\s*"?(?:assms|prems|this|that|hyps|facts|\?thesis|IH\d*|local\.)',
    re.IGNORECASE,
)

_STRUCTURE_RE = re.compile(
    r"("
    r"illegal\s+application\s+of\s+proof\s+command"
    r"|failed\s+to\s+finish\s+proof"
    r"|unfinished\s+proof"
    r"|attempt\s+to\s+refine"
    r"|outer\s+syntax\s+error"
    r"|not\s+a\s+proof"
    r"|bad\s+context"
    r")",
    re.IGNORECASE,
)


def classify_verify_failure(
    error_text: str,
    *,
    known_lemmas: Optional[Sequence[str]] = None,
) -> str:
    """判定验证失败根因：missing_lemma 或 structure_error。"""
    text = error_text or ""
    if _LOCAL_FACT_RE.search(text):
        return STRUCTURE_ERROR
    if _MISSING_LEMMA_RE.search(text):
        return MISSING_LEMMA
    del known_lemmas  # 预留：规则无法判定时可由调用方用大模型兜底
    if _STRUCTURE_RE.search(text):
        return STRUCTURE_ERROR
    return STRUCTURE_ERROR


def failure_rationale(error_text: str) -> str:
    """给出规则判定的简要依据（用于日志与产物）。"""
    text = error_text or ""
    m = _LOCAL_FACT_RE.search(text)
    if m:
        return f"local proof fact used out of scope: {m.group(0)}"
    m = _MISSING_LEMMA_RE.search(text)
    if m:
        return f"matched missing-lemma signal: {m.group(0)}"
    m = _STRUCTURE_RE.search(text)
    if m:
        return f"matched structure signal: {m.group(0)}"
    return "no explicit signal; default to structure_error"