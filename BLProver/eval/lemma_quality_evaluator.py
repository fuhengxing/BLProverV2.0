"""
引理质量评估编排器：聚合各维度（语法复杂度、证明推导难度等）。
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from ..config import LemmaQualityEvalConfig
from ..llm.base import LLMInterface
from .common import (
    STAGE_PROVEN_LIBRARY,
    STAGE_PROVEN_LIBRARY_LABEL,
    STAGE_STEP1,
    STAGE_STEP3,
    build_batch_items,
)
from .lemma_reuse import LemmaUsageHistory, LemmaReuseScorer
from .quality_scale import Q_SCALE
from .models import (
    LemmaLibraryQualityReport,
    LemmaQualityBundle,
    LemmaQualityScore,
    ProvenLemmaLibraryQualityReport,
    ProofDifficultyReport,
    ProofDifficultyResult,
    ProofDifficultyV2Report,
    ProofDifficultyV2Result,
    StageProofDifficultyReport,
    StageProofDifficultyV2Report,
    StageSyntaxReport,
    SyntaxComplexityReport,
    SyntaxComplexityResult,
)
from .proof_difficulty_score import ProofDifficultyScorer
from .proof_difficulty_score_v2 import ProofDifficultyV2Scorer
from .proof_difficulty_score_v2.thy_extract import (
    load_decl_blocks_from_thy,
    merge_decl_blocks_from_thy_files,
)
from .syntax_complexity import (
    BatchAnalysisItem,
    analyze_statements_batch,
    normalize_statement_block,
)
from ..utils.lemma_dedup import extract_fact_name

logger = logging.getLogger(__name__)


def _summarize_syntax_stage(
    stage: str, items: List[SyntaxComplexityResult]
) -> StageSyntaxReport:
    ok = [x for x in items if x.success]
    nodes = [x.prop_nodes for x in ok]
    report = StageSyntaxReport(
        stage=stage,
        total=len(items),
        succeeded=len(ok),
        failed=len(items) - len(ok),
        items=items,
    )
    if nodes:
        report.prop_nodes_min = min(nodes)
        report.prop_nodes_max = max(nodes)
        report.prop_nodes_mean = round(sum(nodes) / len(nodes), 2)
    return report


def _summarize_proof_stage(
    stage: str, items: List[ProofDifficultyResult]
) -> StageProofDifficultyReport:
    ok = [x for x in items if x.success]
    scores = [x.total_score for x in ok]
    report = StageProofDifficultyReport(
        stage=stage,
        total=len(items),
        succeeded=len(ok),
        failed=len(items) - len(ok),
        items=items,
    )
    if scores:
        report.total_score_min = min(scores)
        report.total_score_max = max(scores)
        report.total_score_mean = round(sum(scores) / len(scores), 2)
    return report


def _syntax_results_from_batch(
    stage: str,
    batch_items: List[BatchAnalysisItem],
    batch_results: Dict[str, Tuple],
) -> List[SyntaxComplexityResult]:
    out: List[SyntaxComplexityResult] = []
    for bi in batch_items:
        _name, _kind, _inject, preview = normalize_statement_block(
            bi.statement, inline_name=bi.inline_name
        )
        stats, err_log = batch_results.get(bi.item_id, (None, "missing result"))
        if stats:
            out.append(
                SyntaxComplexityResult(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=stats.short_name,
                    kind=stats.kind,
                    prop_nodes=stats.prop_nodes,
                    source=stats.source,
                    success=True,
                    depth=getattr(stats, "depth", 0),
                    quant_conn=getattr(stats, "quant_conn", 0),
                    var_count=getattr(stats, "var_count", 0),
                )
            )
        else:
            out.append(
                SyntaxComplexityResult(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=_name,
                    kind=_kind,
                    prop_nodes=-1,
                    success=False,
                    error=(err_log or "unknown")[:2000],
                )
            )
    return out


def _summarize_proof_v2_stage(
    stage: str, items: List[ProofDifficultyV2Result]
) -> StageProofDifficultyV2Report:
    ok = [x for x in items if x.success]
    counts = [x.used_lemma_count for x in ok]
    report = StageProofDifficultyV2Report(
        stage=stage,
        total=len(items),
        succeeded=len(ok),
        failed=len(items) - len(ok),
        items=items,
    )
    if counts:
        report.used_lemma_count_min = min(counts)
        report.used_lemma_count_max = max(counts)
        report.used_lemma_count_mean = round(sum(counts) / len(counts), 2)
        report.proof_difficulty_score_min = report.used_lemma_count_min
        report.proof_difficulty_score_max = report.used_lemma_count_max
        report.proof_difficulty_score_mean = report.used_lemma_count_mean
    return report


def _proof_v2_results_from_batch(
    stage: str,
    batch_items: List[BatchAnalysisItem],
    batch_results: Dict[str, Tuple],
) -> List[ProofDifficultyV2Result]:
    out: List[ProofDifficultyV2Result] = []
    for bi in batch_items:
        name, _kind, _inject, preview = normalize_statement_block(
            bi.statement, inline_name=bi.inline_name
        )
        count, names, err = batch_results.get(bi.item_id, (0, [], "missing"))
        if err:
            out.append(
                ProofDifficultyV2Result(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=name,
                    success=False,
                    error=err[:2000],
                )
            )
        else:
            out.append(
                ProofDifficultyV2Result(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=name,
                    used_lemma_count=count,
                    used_lemmas=names,
                    success=True,
                )
            )
    return out


def _proof_results_from_batch(
    stage: str,
    batch_items: List[BatchAnalysisItem],
    batch_results: Dict[str, Tuple],
) -> List[ProofDifficultyResult]:
    out: List[ProofDifficultyResult] = []
    for bi in batch_items:
        name, _kind, _inject, preview = normalize_statement_block(
            bi.statement, inline_name=bi.inline_name
        )
        score, err, _raw = batch_results.get(bi.item_id, (None, "missing", ""))
        if score and not score.error:
            out.append(
                ProofDifficultyResult(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=name,
                    logic_complexity=score.logic_complexity,
                    proof_technique=score.proof_technique,
                    domain_knowledge=score.domain_knowledge,
                    proof_length=score.proof_length,
                    edge_case_risk=score.edge_case_risk,
                    total_score=score.total_score,
                    reason=score.reason,
                    success=True,
                )
            )
        else:
            out.append(
                ProofDifficultyResult(
                    lemma_id=bi.item_id,
                    stage=stage,
                    statement_preview=preview,
                    lemma_name=name,
                    success=False,
                    error=(err or (score.error if score else "unknown"))[:2000],
                )
            )
    return out


class LemmaQualityEvaluator:
    """引理质量多维度评估。"""

    def __init__(
        self,
        config: Optional[LemmaQualityEvalConfig] = None,
        llm: Optional[LLMInterface] = None,
    ):
        self.config = config or LemmaQualityEvalConfig()
        self.llm = llm

    def evaluate_syntax(
        self,
        theorem_name: str,
        thy_path: Path,
        stage1_statements: List[str],
        stage3_statements: List[str],
        *,
        server_pool: Optional[Any] = None,
    ) -> SyntaxComplexityReport:
        if not thy_path.exists():
            return SyntaxComplexityReport(
                theorem_name=theorem_name,
                thy_path=str(thy_path),
                skipped=True,
                skip_reason=f"上下文理论不存在: {thy_path}",
            )

        items_s1 = build_batch_items(stage1_statements, STAGE_STEP1)
        items_s3 = build_batch_items(stage3_statements, STAGE_STEP3)
        all_items = items_s1 + items_s3

        report = SyntaxComplexityReport(
            theorem_name=theorem_name,
            thy_path=str(thy_path.resolve()),
        )
        if not all_items:
            report.stage1 = _summarize_syntax_stage(STAGE_STEP1, [])
            report.stage3 = _summarize_syntax_stage(STAGE_STEP3, [])
            return report

        logger.info(
            "语法复杂度批量评估：%d 条（step1=%d, step3=%d），单 Isabelle server",
            len(all_items),
            len(items_s1),
            len(items_s3),
        )
        batch_results = analyze_statements_batch(
            thy_path,
            all_items,
            timeout=self.config.syntax_timeout,
            server_pool=server_pool,
        )
        report.stage1 = _summarize_syntax_stage(
            STAGE_STEP1,
            _syntax_results_from_batch(STAGE_STEP1, items_s1, batch_results),
        )
        report.stage3 = _summarize_syntax_stage(
            STAGE_STEP3,
            _syntax_results_from_batch(STAGE_STEP3, items_s3, batch_results),
        )
        return report

    def evaluate_proof_difficulty(
        self,
        theorem_name: str,
        stage1_statements: List[str],
        stage3_statements: List[str],
    ) -> ProofDifficultyReport:
        if not self.llm:
            return ProofDifficultyReport(
                theorem_name=theorem_name,
                skipped=True,
                skip_reason="未提供 LLM，无法执行证明推导难度评估",
            )

        items_s1 = build_batch_items(stage1_statements, STAGE_STEP1)
        items_s3 = build_batch_items(stage3_statements, STAGE_STEP3)
        all_items = items_s1 + items_s3

        report = ProofDifficultyReport(
            theorem_name=theorem_name,
            prompt_path=self.config.proof_difficulty_prompt_path,
        )
        if not all_items:
            report.stage1 = _summarize_proof_stage(STAGE_STEP1, [])
            report.stage3 = _summarize_proof_stage(STAGE_STEP3, [])
            return report

        scorer = ProofDifficultyScorer(
            self.llm,
            prompt_path=self.config.proof_difficulty_prompt_path,
        )
        pairs = [(bi.item_id, bi.statement) for bi in all_items]
        logger.info(
            "证明推导难度评估：%d 条（step1=%d, step3=%d），逐条 LLM 调用",
            len(pairs),
            len(items_s1),
            len(items_s3),
        )
        batch_results = scorer.score_statements_batch(pairs)

        report.stage1 = _summarize_proof_stage(
            STAGE_STEP1,
            _proof_results_from_batch(STAGE_STEP1, items_s1, batch_results),
        )
        report.stage3 = _summarize_proof_stage(
            STAGE_STEP3,
            _proof_results_from_batch(STAGE_STEP3, items_s3, batch_results),
        )
        return report

    def evaluate_proof_difficulty_v2(
        self,
        theorem_name: str,
        sketch_thy_path: Path,
        stage1_statements: List[str],
        stage3_statements: List[str],
        *,
        unproven_lemmas_path: Optional[Path] = None,
        evaluated_after: str = "lemma_proving",
    ) -> ProofDifficultyV2Report:
        items_s1 = build_batch_items(stage1_statements, STAGE_STEP1)
        items_s3 = build_batch_items(stage3_statements, STAGE_STEP3)
        all_items = items_s1 + items_s3

        unproven = unproven_lemmas_path if unproven_lemmas_path else None
        thy_blocks = merge_decl_blocks_from_thy_files(sketch_thy_path, unproven)
        primary_thy = unproven if unproven and unproven.is_file() else sketch_thy_path
        report = ProofDifficultyV2Report(
            theorem_name=theorem_name,
            thy_path=str(primary_thy.resolve()) if primary_thy.exists() else str(primary_thy),
            sketch_thy_path=(
                str(sketch_thy_path.resolve())
                if sketch_thy_path.exists()
                else str(sketch_thy_path)
            ),
            unproven_lemmas_path=(
                str(unproven.resolve()) if unproven and unproven.is_file() else ""
            ),
            evaluated_after=evaluated_after,
        )
        if not all_items:
            report.stage1 = _summarize_proof_v2_stage(STAGE_STEP1, [])
            report.stage3 = _summarize_proof_v2_stage(STAGE_STEP3, [])
            return report

        if not thy_blocks:
            report.skipped = True
            report.skip_reason = "未从 sketch/unproven .thy 解析到引理块"
            report.stage1 = _summarize_proof_v2_stage(STAGE_STEP1, [])
            report.stage3 = _summarize_proof_v2_stage(STAGE_STEP3, [])
            return report

        scorer = ProofDifficultyV2Scorer()
        pairs = [(bi.item_id, bi.statement) for bi in all_items]
        logger.info(
            "证明推导难度评分（引理使用计数）：%d 条（step1=%d, step3=%d），"
            "thy 块 %d 个（sketch=%s, unproven=%s）",
            len(pairs),
            len(items_s1),
            len(items_s3),
            len(thy_blocks),
            sketch_thy_path,
            unproven or "(none)",
        )
        batch_results = scorer.score_statements_batch(pairs, thy_blocks=thy_blocks)

        report.stage1 = _summarize_proof_v2_stage(
            STAGE_STEP1,
            _proof_v2_results_from_batch(STAGE_STEP1, items_s1, batch_results),
        )
        report.stage3 = _summarize_proof_v2_stage(
            STAGE_STEP3,
            _proof_v2_results_from_batch(STAGE_STEP3, items_s3, batch_results),
        )
        return report

    def evaluate_proven_lemma_library(
        self,
        proven_thy_path: Path,
        *,
        triggered_by_theorem: str = "",
        server_pool: Optional[Any] = None,
    ) -> ProvenLemmaLibraryQualityReport:
        """对全局 proven_lemmas.thy 中全部已证引理做质量评估。"""
        blocks = (
            list(load_decl_blocks_from_thy(proven_thy_path).values())
            if proven_thy_path.is_file()
            else []
        )
        report = ProvenLemmaLibraryQualityReport(
            thy_path=str(proven_thy_path.resolve())
            if proven_thy_path.exists()
            else str(proven_thy_path),
            triggered_by_theorem=triggered_by_theorem,
            lemma_count=len(blocks),
        )
        if not blocks:
            report.skipped = True
            report.skip_reason = "proven_lemmas.thy 中尚无引理"
            return report

        items = build_batch_items(blocks, STAGE_PROVEN_LIBRARY)
        if self.config.syntax_enabled:
            syntax_report = SyntaxComplexityReport(
                theorem_name="proven_lemma_library",
                thy_path=report.thy_path,
            )
            batch_results = analyze_statements_batch(
                proven_thy_path,
                items,
                timeout=self.config.syntax_timeout,
                server_pool=server_pool,
            )
            syntax_report.stage1 = _summarize_syntax_stage(
                STAGE_PROVEN_LIBRARY,
                _syntax_results_from_batch(STAGE_PROVEN_LIBRARY, items, batch_results),
            )
            report.syntax = syntax_report

        if self.config.proof_difficulty_v2_enabled:
            thy_blocks = load_decl_blocks_from_thy(proven_thy_path)
            pd2 = ProofDifficultyV2Report(
                theorem_name="proven_lemma_library",
                thy_path=report.thy_path,
                evaluated_after="theorem_success",
            )
            scorer = ProofDifficultyV2Scorer()
            pairs = [(bi.item_id, bi.statement) for bi in items]
            batch_results = scorer.score_statements_batch(pairs, thy_blocks=thy_blocks)
            pd2.stage1 = _summarize_proof_v2_stage(
                STAGE_PROVEN_LIBRARY,
                _proof_v2_results_from_batch(STAGE_PROVEN_LIBRARY, items, batch_results),
            )
            report.proof_difficulty_v2 = pd2

        return report

    @staticmethod
    def extract_score_inputs_from_proven_report(
        report: ProvenLemmaLibraryQualityReport,
    ) -> tuple[Dict[str, int], Dict[str, int]]:
        """从 proven 库质量评估报告提取 S(i)/D(i) 字典，供 Q(i) 持久化。

        S(i) 取论文 3.1.3 的四子维度加权值；D(i) 此处仍为报告中的直接引用数，
        主流程会用依赖图的依赖闭包值覆盖（论文 3.1.1）。
        """
        syntax_results: Dict[str, int] = {}
        proof_difficulty_results: Dict[str, int] = {}
        if report.syntax and report.syntax.stage1:
            for item in report.syntax.stage1.items:
                if item.success and item.prop_nodes >= 0 and item.lemma_name:
                    syntax_results[item.lemma_name] = item.weighted_s()
        if report.proof_difficulty_v2 and report.proof_difficulty_v2.stage1:
            for item in report.proof_difficulty_v2.stage1.items:
                if item.success and item.lemma_name:
                    proof_difficulty_results[item.lemma_name] = item.used_lemma_count
        return syntax_results, proof_difficulty_results

    def compute_proven_library_scores(
        self,
        output_dir: str | Path,
        *,
        syntax_results: Optional[Dict[str, int]] = None,
        proof_difficulty_results: Optional[Dict[str, int]] = None,
        reuse_counts: Optional[Dict[str, int]] = None,
    ) -> LemmaLibraryQualityReport:
        """
        使用已缓存的 S(i)、D(i)、U(i) 计算综合质量分 Q(i)。
        返回包含所有引理 S/D/U/Q 的报告。
        """
        from ..lemma.proven_lemma_store import (
            ProvenLemmaStore as Store,
            _load_quality_scores,
        )
        from .lemma_reuse import LemmaUsageHistory

        path = Store.global_thy_path(output_dir)
        blocks = Store.list_lemma_blocks(output_dir)

        report = LemmaLibraryQualityReport(
            thy_path=str(path.resolve()) if path.exists() else str(path),
            lemma_count=len(blocks),
        )

        if not blocks:
            report.skipped = True
            report.skip_reason = "proven_lemmas.thy 中尚无引理"
            return report

        # 若未传任何评分，尝试从持久化缓存读取
        if (
            syntax_results is None
            and proof_difficulty_results is None
            and reuse_counts is None
        ):
            cached = _load_quality_scores(output_dir)
            if cached:
                for name, vals in cached.items():
                    lqs = LemmaQualityScore(
                        lemma_name=name,
                        s=vals.get("s", 0),
                        d=vals.get("d", 1),
                        u=vals.get("u", 1),
                        q=vals.get("q", 0.0),
                    )
                    report.scores[name] = lqs
                return report

        history = LemmaUsageHistory(output_dir)
        names = [extract_fact_name(blk) for blk in blocks]
        names = [n for n in names if n]

        for name in names:
            s = (syntax_results or {}).get(name, 0) if syntax_results else 0
            d = (
                (proof_difficulty_results or {}).get(name, 1)
                if proof_difficulty_results
                else 1
            )
            u = reuse_counts.get(name, 1) if reuse_counts else history.get_reuse_count(name)
            if u <= 0:
                u = 1
            if d <= 0:
                d = 1
            lqs = LemmaQualityScore(lemma_name=name, s=s, d=d, u=u)
            lqs.compute()
            report.scores[name] = lqs

        return report

    @staticmethod
    def save_report(report: Any, path: str | Path) -> None:
        """将质量评估报告序列化写入 JSON 文件。"""
        out = Path(path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(
            json.dumps(report.to_dict(), ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

    @staticmethod
    def print_proven_library_summary(
        report: ProvenLemmaLibraryQualityReport,
    ) -> None:
        if report.skipped:
            print(f"[lemma-quality/proven_library] 跳过: {report.skip_reason}")
            return
        print("\n" + "=" * 72)
        print("【全局已证引理库 proven_lemmas.thy · 质量评估】")
        print(f"  thy: {report.thy_path}")
        print(f"  触发定理: {report.triggered_by_theorem}")
        print(f"  引理条数: {report.lemma_count}")
        if report.syntax and not report.syntax.skipped and report.syntax.stage1:
            LemmaQualityEvaluator._print_proven_library_syntax(report.syntax)
        if (
            report.proof_difficulty_v2
            and not report.proof_difficulty_v2.skipped
            and report.proof_difficulty_v2.stage1
        ):
            LemmaQualityEvaluator._print_proven_library_proof_v2(
                report.proof_difficulty_v2
            )
        print("=" * 72 + "\n")

    @staticmethod
    def print_library_quality_report(report: LemmaLibraryQualityReport) -> None:
        """打印三维综合质量分报告。"""
        if report.skipped:
            print(f"[lemma-quality/proven_library] 跳过: {report.skip_reason}")
            return
        print("\n" + "=" * 72)
        print("【全局已证引理库 · 三维综合质量分】")
        print(f"  thy: {report.thy_path}")
        print(f"  触发定理: {report.triggered_by_theorem}")
        print(f"  引理条数: {report.lemma_count}")
        print()
        print("  ┌─ 维度说明:")
        print("  │  S(i) = 语法复杂度 (prop_nodes)")
        print("  │  D(i) = 证明推导难度 (used_lemma_count)")
        print("  │  U(i) = 引理复用性 (被不同定理引用的次数)")
        print(f"  │  Q(i) = {Q_SCALE:.0f} * U(i) * D(i) / S(i)")
        print("  └─")
        print()
        q_vals = [s.q for s in report.scores.values()]
        if q_vals:
            print(
                f"  Q(i) 统计: min={report.q_min:.2f}, "
                f"max={report.q_max:.2f}, mean={report.q_mean:.2f}"
            )
        print()
        col = "{:<28s} {:>8s} {:>8s} {:>8s} {:>12s}".format
        print("  " + col("引理名", "S(i)", "D(i)", "U(i)", "Q(i)"))
        print("  " + "-" * 66)
        for name in sorted(report.scores.keys()):
            s = report.scores[name]
            print(
                f"  {s.lemma_name:<28s} {s.s:>8d} {s.d:>8d} {s.u:>8d} {s.q:>12.2f}"
            )
        print("=" * 72 + "\n")

    @staticmethod
    def _print_proven_library_syntax(report: SyntaxComplexityReport) -> None:
        stage = report.stage1
        if not stage:
            return
        print(f"\n  维度1 · 语法复杂度 prop_nodes · {STAGE_PROVEN_LIBRARY_LABEL}:")
        print(
            f"    条数 {stage.total}, 成功 {stage.succeeded}, 失败 {stage.failed}"
        )
        if stage.prop_nodes_mean is not None:
            print(
                f"    prop_nodes: min={stage.prop_nodes_min}, "
                f"max={stage.prop_nodes_max}, mean={stage.prop_nodes_mean}"
            )
        for item in stage.items:
            if item.success:
                print(
                    f"      [{item.lemma_id}] {item.lemma_name}: "
                    f"prop_nodes={item.prop_nodes}"
                )
            else:
                print(f"      [{item.lemma_id}] FAILED: {item.error}")

    @staticmethod
    def _print_proven_library_proof_v2(report: ProofDifficultyV2Report) -> None:
        stage = report.stage1
        if not stage:
            return
        print(
            f"\n  维度2 · 证明推导难度 proof_difficulty_score · "
            f"{STAGE_PROVEN_LIBRARY_LABEL}:"
        )
        if report.evaluated_after:
            print(f"    评估时机: {report.evaluated_after}")
        print(
            f"    条数 {stage.total}, 成功 {stage.succeeded}, 失败 {stage.failed}"
        )
        if stage.used_lemma_count_mean is not None:
            print(
                f"    proof_difficulty_score: min={stage.proof_difficulty_score_min}, "
                f"max={stage.proof_difficulty_score_max}, "
                f"mean={stage.proof_difficulty_score_mean}"
            )
        for item in stage.items:
            if item.success:
                print(
                    f"      [{item.lemma_id}] {item.lemma_name}: "
                    f"proof_difficulty_score={item.used_lemma_count} "
                    f"used_lemmas={item.used_lemmas}"
                )
            else:
                print(f"      [{item.lemma_id}] FAILED: {item.error}")

    @staticmethod
    def _print_syntax_summary(report: SyntaxComplexityReport) -> None:
        if report.skipped:
            print(f"[lemma-quality/syntax] 跳过: {report.skip_reason}")
            return
        print("\n" + "=" * 72)
        print("【引理质量评估 · 维度1 语法复杂度 prop_nodes】")
        print(f"  定理: {report.theorem_name}")
        print(f"  上下文: {report.thy_path}")
        for label, stage_report in (
            ("阶段1 (construct_lemmas1)", report.stage1),
            ("阶段3 (construct_lemmas2)", report.stage3),
        ):
            if not stage_report:
                continue
            print(f"\n  {label}:")
            print(
                f"    条数 {stage_report.total}, 成功 {stage_report.succeeded}, "
                f"失败 {stage_report.failed}"
            )
            if stage_report.prop_nodes_mean is not None:
                print(
                    f"    prop_nodes: min={stage_report.prop_nodes_min}, "
                    f"max={stage_report.prop_nodes_max}, "
                    f"mean={stage_report.prop_nodes_mean}"
                )
            for item in stage_report.items:
                if item.success:
                    print(
                        f"      [{item.lemma_id}] {item.lemma_name}: "
                        f"prop_nodes={item.prop_nodes}"
                    )
                else:
                    print(f"      [{item.lemma_id}] FAILED: {item.error}")
        print("=" * 72)

    @staticmethod
    def _print_proof_summary(report: ProofDifficultyReport) -> None:
        if report.skipped:
            print(f"[lemma-quality/proof_difficulty] 跳过: {report.skip_reason}")
            return
        print("\n" + "=" * 72)
        print("【引理质量评估 · 维度2 证明推导难度 total_score】")
        print(f"  定理: {report.theorem_name}")
        print(f"  prompt: {report.prompt_path}")
        for label, stage_report in (
            ("阶段1 (construct_lemmas1)", report.stage1),
            ("阶段3 (construct_lemmas2)", report.stage3),
        ):
            if not stage_report:
                continue
            print(f"\n  {label}:")
            print(
                f"    条数 {stage_report.total}, 成功 {stage_report.succeeded}, "
                f"失败 {stage_report.failed}"
            )
            if stage_report.total_score_mean is not None:
                print(
                    f"    total_score: min={stage_report.total_score_min}, "
                    f"max={stage_report.total_score_max}, "
                    f"mean={stage_report.total_score_mean}"
                )
            for item in stage_report.items:
                if item.success:
                    print(
                        f"      [{item.lemma_id}] {item.lemma_name}: "
                        f"total_score={item.total_score} "
                        f"(logic={item.logic_complexity}, tech={item.proof_technique})"
                    )
                else:
                    print(f"      [{item.lemma_id}] FAILED: {item.error}")
        print("=" * 72 + "\n")

    @staticmethod
    def _print_proof_v2_summary(report: ProofDifficultyV2Report) -> None:
        if report.skipped:
            print(f"[lemma-quality/proof_difficulty_v2] 跳过: {report.skip_reason}")
            return
        print("\n" + "=" * 72)
        print("【引理质量评估 · 证明推导难度 proof_difficulty_score（引理使用计数）】")
        print(f"  定理: {report.theorem_name}")
        print(f"  评分字段: {report.score_field}（= proof_difficulty_score）")
        if report.evaluated_after:
            print(f"  评估时机: {report.evaluated_after}")
        if report.unproven_lemmas_path:
            print(f"  unproven: {report.unproven_lemmas_path}")
        if report.sketch_thy_path:
            print(f"  sketch: {report.sketch_thy_path}")
        elif report.thy_path:
            print(f"  thy: {report.thy_path}")
        for label, stage_report in (
            ("阶段1 (construct_lemmas1)", report.stage1),
            ("阶段3 (construct_lemmas2)", report.stage3),
        ):
            if not stage_report:
                continue
            print(f"\n  {label}:")
            print(
                f"    条数 {stage_report.total}, 成功 {stage_report.succeeded}, "
                f"失败 {stage_report.failed}"
            )
            if stage_report.used_lemma_count_mean is not None:
                print(
                    f"    proof_difficulty_score: min={stage_report.proof_difficulty_score_min}, "
                    f"max={stage_report.proof_difficulty_score_max}, "
                    f"mean={stage_report.proof_difficulty_score_mean}"
                )
            for item in stage_report.items:
                if item.success:
                    print(
                        f"      [{item.lemma_id}] {item.lemma_name}: "
                        f"proof_difficulty_score={item.proof_difficulty_score} "
                        f"used_lemmas={len(item.used_lemmas)}"
                    )
                else:
                    print(f"      [{item.lemma_id}] FAILED: {item.error}")
        print("=" * 72 + "\n")
