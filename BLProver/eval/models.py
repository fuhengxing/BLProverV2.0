"""
引理质量评估 — 数据模型（多维度）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from .quality_scale import Q_SCALE


# --- 维度 1：语法复杂度 ---


@dataclass
class SyntaxComplexityResult:
    lemma_id: str
    stage: str
    statement_preview: str
    lemma_name: str
    kind: str
    prop_nodes: int
    source: str = "isabelle_server/Term.size_of_term"
    success: bool = True
    error: Optional[str] = None
    depth: int = 0
    """论文 3.1.3 子维度 2：语法树深度。"""
    quant_conn: int = 0
    """论文 3.1.3 子维度 3：量词与逻辑连接词数量。"""
    var_count: int = 0
    """论文 3.1.3 子维度 4：变量数量。"""

    def weighted_s(self) -> int:
        """论文 3.1.3：S(i) = 1*节点总数 + 2*深度 + 2*量词与连接词数 + 1*变量数。"""
        from .syntax_complexity.analyzer import SYNTAX_WEIGHTS

        return (
            SYNTAX_WEIGHTS["nodes"] * int(self.prop_nodes)
            + SYNTAX_WEIGHTS["depth"] * int(self.depth)
            + SYNTAX_WEIGHTS["quant_conn"] * int(self.quant_conn)
            + SYNTAX_WEIGHTS["var_count"] * int(self.var_count)
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lemma_id": self.lemma_id,
            "stage": self.stage,
            "statement_preview": self.statement_preview,
            "lemma_name": self.lemma_name,
            "kind": self.kind,
            "prop_nodes": self.prop_nodes,
            "depth": self.depth,
            "quant_conn": self.quant_conn,
            "var_count": self.var_count,
            "s": self.weighted_s(),
            "source": self.source,
            "success": self.success,
            "error": self.error,
        }


@dataclass
class StageSyntaxReport:
    stage: str
    total: int = 0
    succeeded: int = 0
    failed: int = 0
    prop_nodes_min: Optional[int] = None
    prop_nodes_max: Optional[int] = None
    prop_nodes_mean: Optional[float] = None
    items: List[SyntaxComplexityResult] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage,
            "total": self.total,
            "succeeded": self.succeeded,
            "failed": self.failed,
            "prop_nodes_min": self.prop_nodes_min,
            "prop_nodes_max": self.prop_nodes_max,
            "prop_nodes_mean": self.prop_nodes_mean,
            "items": [x.to_dict() for x in self.items],
        }


@dataclass
class SyntaxComplexityReport:
    theorem_name: str
    thy_path: str
    dimension: str = "syntax_complexity"
    stage1: Optional[StageSyntaxReport] = None
    stage3: Optional[StageSyntaxReport] = None
    skipped: bool = False
    skip_reason: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "theorem_name": self.theorem_name,
            "thy_path": self.thy_path,
            "dimension": self.dimension,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "stage1": self.stage1.to_dict() if self.stage1 else None,
            "stage3": self.stage3.to_dict() if self.stage3 else None,
        }


# 兼容旧名
LemmaQualityReport = SyntaxComplexityReport


# --- 维度 2：证明推导难度 ---


@dataclass
class ProofDifficultyResult:
    lemma_id: str
    stage: str
    statement_preview: str
    lemma_name: str
    logic_complexity: int = 0
    proof_technique: int = 0
    domain_knowledge: int = 0
    proof_length: int = 0
    edge_case_risk: int = 0
    total_score: int = 0
    reason: str = ""
    source: str = "llm/proof_difficulty_prompt"
    success: bool = True
    error: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lemma_id": self.lemma_id,
            "stage": self.stage,
            "statement_preview": self.statement_preview,
            "lemma_name": self.lemma_name,
            "logic_complexity": self.logic_complexity,
            "proof_technique": self.proof_technique,
            "domain_knowledge": self.domain_knowledge,
            "proof_length": self.proof_length,
            "edge_case_risk": self.edge_case_risk,
            "total_score": self.total_score,
            "reason": self.reason,
            "source": self.source,
            "success": self.success,
            "error": self.error,
        }


@dataclass
class StageProofDifficultyReport:
    stage: str
    total: int = 0
    succeeded: int = 0
    failed: int = 0
    total_score_min: Optional[int] = None
    total_score_max: Optional[int] = None
    total_score_mean: Optional[float] = None
    items: List[ProofDifficultyResult] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage,
            "total": self.total,
            "succeeded": self.succeeded,
            "failed": self.failed,
            "total_score_min": self.total_score_min,
            "total_score_max": self.total_score_max,
            "total_score_mean": self.total_score_mean,
            "items": [x.to_dict() for x in self.items],
        }


@dataclass
class ProofDifficultyReport:
    theorem_name: str
    dimension: str = "proof_difficulty"
    prompt_path: str = ""
    stage1: Optional[StageProofDifficultyReport] = None
    stage3: Optional[StageProofDifficultyReport] = None
    skipped: bool = False
    skip_reason: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "theorem_name": self.theorem_name,
            "dimension": self.dimension,
            "prompt_path": self.prompt_path,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "stage1": self.stage1.to_dict() if self.stage1 else None,
            "stage3": self.stage3.to_dict() if self.stage3 else None,
        }


# --- 维度 2b：证明引理使用计数（v2，非 LLM） ---


@dataclass
class ProofDifficultyV2Result:
    lemma_id: str
    stage: str
    statement_preview: str
    lemma_name: str
    used_lemma_count: int = 0
    """证明推导难度评分：证明中显式引用的库引理个数（去重）。"""
    used_lemmas: List[str] = field(default_factory=list)
    """引理名列表，按在证明中首次出现的顺序。"""
    source: str = "proof_difficulty_score_v2/used_lemma_count"
    success: bool = True
    error: Optional[str] = None

    @property
    def proof_difficulty_score(self) -> int:
        """与 used_lemma_count 相同，便于结果 JSON 中作为「证明推导难度」读取。"""
        return self.used_lemma_count

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lemma_id": self.lemma_id,
            "stage": self.stage,
            "statement_preview": self.statement_preview,
            "lemma_name": self.lemma_name,
            "proof_difficulty_score": self.proof_difficulty_score,
            "used_lemma_count": self.used_lemma_count,
            "used_lemmas": self.used_lemmas,
            "source": self.source,
            "success": self.success,
            "error": self.error,
        }


@dataclass
class StageProofDifficultyV2Report:
    stage: str
    total: int = 0
    succeeded: int = 0
    failed: int = 0
    used_lemma_count_min: Optional[int] = None
    used_lemma_count_max: Optional[int] = None
    used_lemma_count_mean: Optional[float] = None
    proof_difficulty_score_min: Optional[int] = None
    proof_difficulty_score_max: Optional[int] = None
    proof_difficulty_score_mean: Optional[float] = None
    items: List[ProofDifficultyV2Result] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage,
            "total": self.total,
            "succeeded": self.succeeded,
            "failed": self.failed,
            "score_field": "used_lemma_count",
            "used_lemma_count_min": self.used_lemma_count_min,
            "used_lemma_count_max": self.used_lemma_count_max,
            "used_lemma_count_mean": self.used_lemma_count_mean,
            "proof_difficulty_score_min": self.proof_difficulty_score_min,
            "proof_difficulty_score_max": self.proof_difficulty_score_max,
            "proof_difficulty_score_mean": self.proof_difficulty_score_mean,
            "items": [x.to_dict() for x in self.items],
        }


@dataclass
class ProofDifficultyV2Report:
    theorem_name: str
    dimension: str = "proof_difficulty"
    metric: str = "used_lemma_count"
    score_field: str = "used_lemma_count"
    thy_path: str = ""
    sketch_thy_path: str = ""
    unproven_lemmas_path: str = ""
    evaluated_after: str = ""
    stage1: Optional[StageProofDifficultyV2Report] = None
    stage3: Optional[StageProofDifficultyV2Report] = None
    skipped: bool = False
    skip_reason: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "theorem_name": self.theorem_name,
            "dimension": self.dimension,
            "metric": self.metric,
            "score_field": self.score_field,
            "score_description": "证明推导难度评分：证明中显式引用的库引理个数（去重、按出现顺序）",
            "implementation": "proof_difficulty_score_v2",
            "thy_path": self.thy_path,
            "sketch_thy_path": self.sketch_thy_path,
            "unproven_lemmas_path": self.unproven_lemmas_path,
            "evaluated_after": self.evaluated_after,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "stage1": self.stage1.to_dict() if self.stage1 else None,
            "stage3": self.stage3.to_dict() if self.stage3 else None,
        }


@dataclass
class LemmaQualityBundle:
    """单次定理运行的多维度引理质量评估汇总（兼容旧数据）。"""

    theorem_name: str
    thy_path: str
    syntax: Optional[SyntaxComplexityReport] = None
    proof_difficulty: Optional[ProofDifficultyReport] = None
    proof_difficulty_v2: Optional[ProofDifficultyV2Report] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "theorem_name": self.theorem_name,
            "thy_path": self.thy_path,
            "syntax_complexity": self.syntax.to_dict() if self.syntax else None,
            "proof_difficulty": self.proof_difficulty.to_dict() if self.proof_difficulty else None,
            "proof_difficulty_v2": (
                self.proof_difficulty_v2.to_dict() if self.proof_difficulty_v2 else None
            ),
        }


@dataclass
class ProvenLemmaLibraryQualityReport:
    """全局 proven_lemmas.thy 库质量评估（定理成功后触发）。"""

    thy_path: str
    triggered_by_theorem: str
    lemma_count: int = 0
    syntax: Optional[SyntaxComplexityReport] = None
    proof_difficulty_v2: Optional[ProofDifficultyV2Report] = None
    skipped: bool = False
    skip_reason: Optional[str] = None

    @property
    def quality_threshold(self) -> int:
        """U * D / S 计算后除以本常量，得分越大越好。"""
        return 1

    def to_dict(self) -> Dict[str, Any]:
        syntax_dict = None
        if self.syntax:
            syntax_dict = self.syntax.to_dict()
            if self.syntax.stage1 and not self.syntax.stage3:
                syntax_dict["library"] = self.syntax.stage1.to_dict()
        pd2_dict = None
        if self.proof_difficulty_v2:
            pd2_dict = self.proof_difficulty_v2.to_dict()
            if self.proof_difficulty_v2.stage1 and not self.proof_difficulty_v2.stage3:
                pd2_dict["library"] = self.proof_difficulty_v2.stage1.to_dict()
        return {
            "thy_path": self.thy_path,
            "triggered_by_theorem": self.triggered_by_theorem,
            "lemma_count": self.lemma_count,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "syntax_complexity": syntax_dict,
            "proof_difficulty_v2": pd2_dict,
        }


@dataclass
class LemmaQualityScore:
    """单条引理的三维质量分。"""

    lemma_name: str
    s: int = 0
    """S(i)：语法复杂度（prop_nodes）。"""
    d: int = 0
    """D(i)：证明推导难度（used_lemma_count）。"""
    u: int = 0
    """U(i)：引理复用性——被多少不同定理的 proof 引用。"""
    q: float = 0.0
    """Q(i) = Q_SCALE * U(i) * D(i) / S(i)（S=0 时 Q=0；Q_SCALE=100，见 eval/quality_scale.py）。"""

    def compute(self) -> None:
        self.q = Q_SCALE * (self.u * self.d) / self.s if self.s > 0 else 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lemma_name": self.lemma_name,
            "S(i)_syntax_complexity": self.s,
            "D(i)_proof_difficulty": self.d,
            "U(i)_reuse_count": self.u,
            "Q(i)_quality_score": round(self.q, 4),
        }


@dataclass
class LemmaLibraryQualityReport:
    """
    全局 proven_lemmas.thy 全库质量评估汇总：S(i)、D(i)、U(i)、Q(i)。
    每次 merge 新引理后更新。
    """

    thy_path: str
    lemma_count: int = 0
    triggered_by_theorem: str = ""
    scores: Dict[str, LemmaQualityScore] = field(default_factory=dict)
    """key=lemma_name -> LemmaQualityScore"""
    skipped: bool = False
    skip_reason: Optional[str] = None

    @property
    def q_min(self) -> float:
        vals = [s.q for s in self.scores.values()]
        return min(vals) if vals else 0.0

    @property
    def q_max(self) -> float:
        vals = [s.q for s in self.scores.values()]
        return max(vals) if vals else 0.0

    @property
    def q_mean(self) -> float:
        vals = [s.q for s in self.scores.values()]
        return round(sum(vals) / len(vals), 4) if vals else 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "thy_path": self.thy_path,
            "triggered_by_theorem": self.triggered_by_theorem,
            "lemma_count": self.lemma_count,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "q_min": round(self.q_min, 4),
            "q_max": round(self.q_max, 4),
            "q_mean": round(self.q_mean, 4),
            "dimensions": {
                "S(i)": {"name": "语法复杂度", "source": "Isabelle size_of_term (prop_nodes)"},
                "D(i)": {"name": "证明推导难度", "source": "used_lemma_count in proof"},
                "U(i)": {"name": "引理复用性", "source": "被不同定理 proof 引用的次数"},
                "Q(i)": {
                    "name": "引理质量分",
                    "formula": "Q(i) = Q_SCALE * U(i) * D(i) / S(i)（Q_SCALE=100）",
                },
            },
            "item_scores": sorted(
                [s.to_dict() for s in self.scores.values()],
                key=lambda x: x["Q(i)_quality_score"],
                reverse=True,
            ),
        }
