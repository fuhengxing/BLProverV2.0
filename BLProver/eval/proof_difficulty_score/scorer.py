"""
维度 2：证明推导难度（LLM 五维评分 + total_score）。

通过 proof_difficulty_prompt.txt 将构造引理发送给大模型，解析 JSON 评分结果。
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from ...llm.base import LLMInterface
from ...sketch.construct_lemma_generator import split_construct_lemma_prompt_file
from ..syntax_complexity import normalize_statement_block

logger = logging.getLogger(__name__)

_USER_PROVIDE = "{{user provide}}"
_SCORE_KEYS = (
    "logic_complexity",
    "proof_technique",
    "domain_knowledge",
    "proof_length",
    "edge_case_risk",
)


@dataclass
class ProofDifficultyScore:
    logic_complexity: int
    proof_technique: int
    domain_knowledge: int
    proof_length: int
    edge_case_risk: int
    total_score: int
    reason: str
    error: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "logic_complexity": self.logic_complexity,
            "proof_technique": self.proof_technique,
            "domain_knowledge": self.domain_knowledge,
            "proof_length": self.proof_length,
            "edge_case_risk": self.edge_case_risk,
            "total_score": self.total_score,
            "reason": self.reason,
            "error": self.error,
        }


def default_prompt_path() -> Path:
    return Path(__file__).resolve().parent / "proof_difficulty_prompt.txt"


def format_lemma_for_prompt(statement: str) -> str:
    text = (statement or "").strip()
    if text.startswith("```"):
        return text
    return f"```isabelle\n{text}\n```"


def fill_lemma_user_prompt(user_template: str, lemma_block: str) -> str:
    if _USER_PROVIDE not in user_template:
        raise ValueError("证明难度 prompt 缺少 {{user provide}} 占位符")
    return user_template.replace(_USER_PROVIDE, lemma_block, 1)


def _extract_json_object(text: str) -> Optional[Dict[str, Any]]:
    raw = (text or "").strip()
    if not raw:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", raw, re.DOTALL | re.IGNORECASE)
    if fence:
        raw = fence.group(1).strip()
    else:
        start = raw.find("{")
        end = raw.rfind("}")
        if start >= 0 and end > start:
            raw = raw[start : end + 1]
    try:
        data = json.loads(raw)
        return data if isinstance(data, dict) else None
    except json.JSONDecodeError:
        return None


def parse_proof_difficulty_response(raw: str) -> Tuple[Optional[ProofDifficultyScore], str]:
    data = _extract_json_object(raw)
    if not data:
        return None, "无法从模型输出解析 JSON"

    if data.get("error"):
        return None, f"{data.get('error')}: {data.get('reason', '')}"

    try:
        dims = {k: int(data[k]) for k in _SCORE_KEYS}
        total = int(data.get("total_score", data.get("overall_score", 0)))
        reason = str(data.get("reason", "")).strip()
    except (KeyError, TypeError, ValueError) as exc:
        return None, f"JSON 字段不完整或类型错误: {exc}"

    for k, v in dims.items():
        if not (1 <= v <= 5):
            return None, f"{k}={v} 不在 1-5 范围内"

    if not (1 <= total <= 10):
        return None, f"total_score={total} 不在 1-10 范围内"

    return (
        ProofDifficultyScore(
            logic_complexity=dims["logic_complexity"],
            proof_technique=dims["proof_technique"],
            domain_knowledge=dims["domain_knowledge"],
            proof_length=dims["proof_length"],
            edge_case_risk=dims["edge_case_risk"],
            total_score=total,
            reason=reason,
        ),
        "",
    )


class ProofDifficultyScorer:
    """调用 LLM 对单条/多条构造引理评分证明推导难度。"""

    def __init__(
        self,
        llm: LLMInterface,
        prompt_path: Optional[str] = None,
    ):
        self.llm = llm
        path = Path(prompt_path or default_prompt_path())
        if not path.is_file():
            raise FileNotFoundError(f"证明难度 prompt 不存在: {path}")
        text = path.read_text(encoding="utf-8")
        self._system_prompt, self._user_template = split_construct_lemma_prompt_file(text)

    def score_statement(self, statement: str) -> Tuple[Optional[ProofDifficultyScore], str]:
        lemma_block = format_lemma_for_prompt(statement)
        user_prompt = fill_lemma_user_prompt(self._user_template, lemma_block)
        raw = self.llm.generate(user_prompt, self._system_prompt)
        return parse_proof_difficulty_response(raw)

    def score_statements_batch(
        self,
        items: List[Tuple[str, str]],
    ) -> Dict[str, Tuple[Optional[ProofDifficultyScore], str, str]]:
        """
        对多条引理依次调用 LLM（每条一次请求，条数 N 无上限）。

        items: [(item_id, statement), ...]
        返回 item_id -> (score, error, raw_response_preview)
        """
        out: Dict[str, Tuple[Optional[ProofDifficultyScore], str, str]] = {}
        for item_id, statement in items:
            text = (statement or "").strip()
            if not text:
                continue
            logger.info("证明推导难度评估 %s", item_id)
            raw = ""
            try:
                lemma_block = format_lemma_for_prompt(text)
                user_prompt = fill_lemma_user_prompt(self._user_template, lemma_block)
                raw = self.llm.generate(user_prompt, self._system_prompt)
                score, err = parse_proof_difficulty_response(raw)
                preview = raw[:500] if raw else ""
                out[item_id] = (score, err, preview)
            except Exception as exc:
                out[item_id] = (None, str(exc), raw[:500])
        return out
