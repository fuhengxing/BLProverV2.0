"""
BLProver CLI 主程序
"""

import json
import re
import argparse
import logging
import time
from pathlib import Path
from typing import Dict, Optional, List, Tuple
from .config import BLProverConfig, LLMConfig, LemmaCacheConfig
from .llm.openai_llm import OpenAILLM
from .lemma import LemmaCache, UnprovenLemmaStore, ProvenLemmaStore, PROVEN_THEORY_NAME, DefinitionStore, LemmasReflectionRunner
from .lemma.domain import resolve_domain, theorem_theory_dir
from .lemma.thy_imports import (
    theorem_final_imports,
    theorem_self_contained_imports,
    theorem_sketch_imports,
)
from .sketch.sketch_generator import SketchGenerator
from .sketch.repair_lemma import RepairLemmaContext, RepairLemmaRunner
from .sketch.sketch_repair import SketchRepairLoopContext, SketchRepairRunner
from .sketch.failure_analysis import (
    MISSING_LEMMA,
    classify_verify_failure,
    failure_rationale,
)
from .lemma_proving import (
    LemmaProofIterator,
    TheoremLemmaUsageReport,
    analyze_theorem_lemma_usage,
    prove_used_lemmas_after_theorem,
)
from .sketch.construct_lemma_generator import (
    ConstructLemmaGenerator,
    parse_construct_lemma_response,
    format_function_definitions_block,
    format_theorem_statement_block,
    split_construct_lemma_prompt_file,
)
from .utils.theorem_run_artifact import TheoremRunArtifact
from .utils.isabelle_sledgehammer import (
    IsabelleRunnerConfig,
    IsabelleServerSessionPool,
    print_thy_verify_result,
    process_sledgehammer_and_verify,
    prepare_session_for_final_theory_verify,
    prepare_session_for_self_contained_verify,
    verify_thy_with_repair,
)
from .utils.lemma_dedup import (
    dedupe_lemma_statements,
    dedupe_lemma_statements_detailed,
    ensure_pri_queue_invariant_lemmas,
    extract_fact_name,
    ensure_main_theorem_declaration,
    merge_sketch_into_theory,
    strip_quick_and_dirty_declarations,
    truncate_theory_to_first_closure,
)
from .eval import LemmaQualityEvaluator
from .eval.quality_screening import (
    SOURCE_GLOBAL,
    SOURCE_MIDDLE,
    SOURCE_REPAIR,
    canonicalize_linear_labels,
    identify_linear_labels,
    load_labels,
    load_state,
    linear_map_from_labels,
    record_labels,
    save_state,
    screen_batch,
    source_map_from_labels,
)
from .utils.isabelle_server_lifecycle import (
    set_kill_orphans_on_shutdown,
    shutdown_all_isabelle_servers,
)
from .utils.run_log import resolve_main_run_log_stem, run_log_path
from .utils.progress import (
    ConsoleLineFilter,
    STAGE_LABEL,
    TOTAL_STAGES,
    attach_stream,
    board,
    format_duration,
    set_verbose,
)

logger = logging.getLogger(__name__)
_USER_PROVIDE = "{{user provide}}"

# 隐藏的 step4 完整证明提示词：优先于配置中的旧提示词，旧文件保持原样。
from .sketch.prompt_paths import HIDDEN_FULL_PROOF_PROMPT as _HIDDEN_STEP4_PROMPT
_ISABELLE_FACT_NAME_RE = re.compile(
    r"^\s*(?:lemma|theorem|corollary)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)


def _extract_isabelle_fact_name(lemma_text: str) -> Optional[str]:
    m = _ISABELLE_FACT_NAME_RE.search((lemma_text or "").strip())
    return m.group(1) if m else None


def _theorem_verified(result: Dict) -> bool:
    """定理是否证明成功（内核验证通过即为成功）。

    论文 4.1.2 主口径：引用只统计「证明成功的定理」，
    证明失败的定理不得计入，也不得触发引理库质量评估与筛选。
    """
    if result.get("final_theorem_verified"):
        return True
    return str(result.get("status") or "") == "theorem_and_used_lemmas_verified"


class _TeeStream:
    """将输出同时写入终端和日志文件。

    ``console_filter`` 只作用于控制台侧（按行过滤内部细节）；
    日志文件侧始终写入全量内容。
    """

    def __init__(self, *streams, console_filter=None):
        self._streams = streams
        self._console = streams[0] if streams else None
        self._file = streams[1] if len(streams) > 1 else None
        self._filter = console_filter

    def write(self, data):
        if self._console is not None:
            if self._filter is None:
                self._console.write(data)
            else:
                visible = self._filter.feed(data)
                if visible:
                    self._console.write(visible)
        if self._file is not None:
            self._file.write(data)
        return len(data)

    def write_file_only(self, data):
        """仅写入日志文件（控制台不显示）。"""
        if self._file is not None:
            self._file.write(data)
            self._file.flush()

    def flush(self):
        if self._console is not None and self._filter is not None:
            pending = self._filter.drain()
            if pending:
                self._console.write(pending)
        for stream in self._streams:
            stream.flush()

    def isatty(self):
        first = self._streams[0] if self._streams else None
        return bool(first and hasattr(first, "isatty") and first.isatty())


_DECLARED_NAME_RE = re.compile(r"^\s*(?:lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)", re.MULTILINE)


def _declared_name(block: str) -> str:
    match = _DECLARED_NAME_RE.search(block or "")
    return match.group(1) if match else ""


class BLProver:
    """BLProver 核心类"""
    
    def __init__(
        self,
        config: Optional[BLProverConfig] = None,
        isabelle_runner: Optional[IsabelleRunnerConfig] = None,
        run_sledgehammer_after_thy: bool = True,
    ):
        """
        初始化 BLProver
        
        Args:
            config: 配置对象
            isabelle_runner: Isabelle/sledgehammer 后处理配置
            run_sledgehammer_after_thy: 生成 .thy 后是否自动执行 sledgehammer 回填与验证
        """
        self.config = config or BLProverConfig()
        self.isabelle_runner = isabelle_runner
        self.run_sledgehammer_after_thy = run_sledgehammer_after_thy
        if isabelle_runner is not None:
            set_kill_orphans_on_shutdown(
                isabelle_runner.kill_orphan_poly_on_shutdown
            )
        
        # 初始化LLM
        self.llm = OpenAILLM(
            model_name=self.config.llm.model_name,
            api_key=self.config.llm.api_key,
            base_url=self.config.llm.base_url,
            temperature=self.config.llm.temperature,
            max_tokens=self.config.llm.max_tokens,
            thinking_mode=self.config.llm.thinking_mode,
            reasoning_effort=self.config.llm.reasoning_effort,
        )
        
        # 引理缓存（Chroma 可选；默认关闭，引理由 .thy 文件管理）
        self.lemma_cache: Optional[LemmaCache]
        if self.config.lemma_cache.chroma_enabled:
            self.lemma_cache = LemmaCache(self.config.lemma_cache)
        else:
            self.lemma_cache = None
        self.unproven_lemma_store = UnprovenLemmaStore(self.config.lemma_cache)

        # 构造引理（非形式化证明 + new lemma）
        self.construct_lemma_generator = ConstructLemmaGenerator(
            self.llm,
            self.config.construct_lemma_prompt_path,
        )

        # 初始化草图生成器
        self.sketch_generator = SketchGenerator(
            self.llm,
            self.lemma_cache,
            sketch_prompt_path=self.config.sketch_prompt_path,
        )

        # 验证失败后的草图迭代修复（见 sketch/sketch_repair.py + prompt/sketch_repair_after_verify_prompt.txt）
        self.sketch_repair = SketchRepairRunner(
            self.config,
            load_prompt_template=self._load_prompt_template,
            call_stage_llm=self._call_stage_llm,
        )

        self.lemmas_reflection = LemmasReflectionRunner(
            self.config,
            load_prompt_template=self._load_prompt_template,
            call_stage_llm=self._call_stage_llm,
        )

        # 论文 2.3.3：修复引理构造策略 + 引理修正机制
        self.repair_lemma = RepairLemmaRunner(
            self.config,
            load_prompt_template=self._load_prompt_template,
            call_stage_llm=self._call_stage_llm,
        )

        self.lemma_proof_iterator = LemmaProofIterator(self.config, self.llm)
        
        logger.info("BLProver 初始化完成")

    def _load_prompt_template(self, prompt_path: str) -> Tuple[str, str]:
        path_obj = Path(prompt_path)
        if not path_obj.is_file():
            raise FileNotFoundError(f"提示词文件不存在: {path_obj}")
        text = path_obj.read_text(encoding="utf-8")
        try:
            return split_construct_lemma_prompt_file(text)
        except ValueError as exc:
            raise ValueError(f"提示词文件格式错误 ({path_obj}): {exc}") from exc

    def _fill_user_provide(
        self,
        user_template: str,
        replacements: List[str],
        prompt_path: str,
    ) -> str:
        placeholder_count = user_template.count(_USER_PROVIDE)
        if placeholder_count != len(replacements):
            raise ValueError(
                f"提示词占位符数量与输入块数量不匹配: {prompt_path}, "
                f"占位符={placeholder_count}, 输入块={len(replacements)}"
            )
        out = user_template
        for block in replacements:
            out = out.replace(_USER_PROVIDE, block, 1)
        return out

    def _call_stage_llm(self, stage_name: str, system_prompt: str, user_prompt: str) -> str:
        start = time.perf_counter()
        raw = self.llm.generate(user_prompt, system_prompt)
        raw = self._sanitize_llm_text(raw, stage_name)
        self._validate_stage_output(stage_name, raw)
        elapsed = time.perf_counter() - start
        logger.info("%s 完成，输出长度=%d，耗时=%.2fs", stage_name, len(raw or ""), elapsed)
        return raw

    def _resolve_step4_prompt_path(self, prompt_path: str) -> Path:
        """返回 step4 实际使用的提示词。

        隐藏的完整证明提示词优先；旧的 ``informalProof_to_formalProof_prompt.txt``
        保持原样不动，仅在隐藏文件缺失时回退。
        """
        if _HIDDEN_STEP4_PROMPT.is_file():
            return _HIDDEN_STEP4_PROMPT
        return Path(prompt_path)

    def _run_step4_formal_sketch(
        self,
        prompt_path: str,
        func_block: str,
        theorem_block: str,
        informal_proof: str,
        available_lemmas: Optional[List[str]] = None,
    ) -> Tuple[str, str]:
        effective_path = self._resolve_step4_prompt_path(prompt_path)
        s4_sys, s4_tpl = self._load_prompt_template(str(effective_path))
        replacements = [func_block, theorem_block, informal_proof]
        if s4_tpl.count(_USER_PROVIDE) >= 4:
            replacements.append(self._format_lemmas_block(available_lemmas or []))
        s4_user = self._fill_user_provide(
            s4_tpl,
            replacements,
            str(effective_path),
        )
        # 对外仍显示旧提示词名，保持既有日志/看板口径。
        logger.info("step4 提示词: %s", Path(prompt_path).name)
        s4_raw = self._call_stage_llm("step4_informal_to_formal", s4_sys, s4_user)
        return self.sketch_generator._clean_sketch(s4_raw), s4_raw

    def _format_lemmas_block(self, lemma_statements: List[str]) -> str:
        if not lemma_statements:
            return "(none)"
        blocks: List[str] = []
        for idx, stmt in enumerate(lemma_statements, start=1):
            text = (stmt or "").strip()
            if not text:
                continue
            blocks.append(f"### new lemma{idx}")
            blocks.append("```isabelle")
            blocks.append(text)
            blocks.append("```")
            blocks.append("")
        return "\n".join(blocks).strip() or "(none)"

    def _normalize_informal_proof(self, raw_text: str) -> str:
        text = (raw_text or "").strip()
        text = re.sub(r"^\s*```(?:text|markdown)?\s*", "", text, flags=re.IGNORECASE)
        text = re.sub(r"\s*```\s*$", "", text)
        text = re.sub(r"^\s*\{\{\s*", "", text)
        text = re.sub(r"\s*\}\}\s*$", "", text)
        return text.strip()

    def _sanitize_llm_text(self, text: str, stage_name: str) -> str:
        """
        清洗 LLM 返回中的兼容性字符，避免 Isabelle/解析流程受不可见字符影响。
        """
        if text is None:
            return ""
        out = str(text)
        original = out
        out = out.replace("\ufeff", "")
        out = out.replace("\u00a0", " ")
        out = out.replace("\u2007", " ")
        out = out.replace("\u202f", " ")
        out = out.replace("\r\n", "\n").replace("\r", "\n")
        if out != original:
            logger.warning(
                "%s 输出包含兼容性字符（如 NBSP/BOM），已自动规范化",
                stage_name,
            )
        bad_controls = [c for c in out if ord(c) < 32 and c not in ("\n", "\t")]
        if bad_controls:
            logger.warning("%s 输出包含控制字符，数量=%d", stage_name, len(bad_controls))
        return out

    def _validate_stage_output(self, stage_name: str, text: str) -> None:
        """
        每阶段做最小格式校验，异常立即抛错，防止坏格式进入 Isabelle 验证链路。
        """
        body = (text or "").strip()
        if not body:
            raise ValueError(f"{stage_name} 返回为空")

        if stage_name in ("step1_construct_lemmas1", "step3_construct_lemmas2"):
            _informal, parsed = parse_construct_lemma_response(body)
            if not parsed:
                raise ValueError(f"{stage_name} 未解析到引理，请检查模型输出格式")
        elif stage_name == "step4_informal_to_formal":
            lowered = body.lower()
            # 隐藏提示词只要求输出证明体（proof/by），不重复 theorem 头；
            # 因此这里同时接受 proof/by，避免误报“不是 Isabelle 文本”。
            if not any(
                key in lowered
                for key in ("theorem ", "lemma ", "proof", " by ", "\nby ")
            ):
                logger.warning(
                    "%s 输出未发现 theorem/lemma/proof 关键字，可能不是 Isabelle 证明文本",
                    stage_name,
                )
    
    def prove_theorem(self, theorem_file: str) -> Dict:
        """
        证明单个定理（含论文 1.4 步骤 5 / 4.3 的外层回溯）。

        定理验证失败时回溯至"草图构建 + 引理生成 + 定理验证"重新执行；
        已证引理库持久化在磁盘上，重试时自动复用（不清空）。
        次数上限 config.theorem_outer_restart_max（默认 3）。
        """
        max_attempts = max(
            1, int(getattr(self.config, "theorem_outer_restart_max", 3))
        )
        history: List[Dict] = []
        result: Dict = {}
        try:
            _theorem_head = self._load_theorem_data(theorem_file)
        except Exception:
            _theorem_head = {}
        _board_name = str(
            _theorem_head.get("theorem name") or Path(theorem_file).stem
        )
        try:
            _board_domain = resolve_domain(_theorem_head, theorem_file)
        except Exception:
            _board_domain = ""
        for attempt in range(1, max_attempts + 1):
            board.begin(
                _board_name,
                domain=_board_domain,
                output_dir=str(getattr(self.config, "output_dir", "") or ""),
                attempt=attempt,
                total_attempts=max_attempts,
            )
            result = self._prove_theorem_once(theorem_file)
            history.append(
                {
                    "attempt": attempt,
                    "status": result.get("status"),
                    "final_theorem_verified": bool(
                        result.get("final_theorem_verified")
                    ),
                }
            )
            result["theorem_outer_attempts"] = attempt
            result["theorem_outer_history"] = history
            if self._theorem_attempt_succeeded(result):
                break
            if attempt < max_attempts:
                logger.warning(
                    "定理外层回溯：第 %d/%d 次未成功（status=%s），复用已证引理库重试",
                    attempt,
                    max_attempts,
                    result.get("status"),
                )
                print(
                    f"\n[outer-retry] 第 {attempt}/{max_attempts} 次未成功"
                    f"（status={result.get('status')}），复用已证引理库重试...",
                    flush=True,
                )
        _succeeded = self._theorem_attempt_succeeded(result)
        board.summary(
            status="成功" if _succeeded else "未成功",
            note="status=%s ｜ 外层尝试 %d/%d"
            % (
                result.get("status"),
                int(result.get("theorem_outer_attempts") or 1),
                max_attempts,
            ),
        )
        return result

    @staticmethod
    def _theorem_attempt_succeeded(result: Dict) -> bool:
        """定理外层一次尝试是否成功（内核验证通过即为成功）。"""
        return _theorem_verified(result)

    def _prove_theorem_once(self, theorem_file: str) -> Dict:
        """证明单个定理（单次尝试）。"""
        logger.info(f"开始证明定理: {theorem_file}")
        
        # 加载定理数据
        theorem_data = self._load_theorem_data(theorem_file)
        theorem_name = theorem_data.get("theorem name", "unknown")
        domain = resolve_domain(theorem_data, theorem_file)
        theorem_data = {**theorem_data, "domain": domain}
        
        result = {
            "theorem_name": theorem_name,
            "status": "failed",
            "sketch": "",
            "final_proof": "",
            "verification_result": None,
            "error": None,
            "construct_lemma_raw": None,
            "constructed_lemma_statements": None,
        }

        try:
            # 1-4. 四阶段提示词流程
            func_block = format_function_definitions_block(theorem_data)
            theorem_block = format_theorem_statement_block(theorem_data)
            if not func_block.strip():
                raise ValueError("缺少 formal function definitions，无法构建阶段提示词")
            if not theorem_block.strip():
                raise ValueError("缺少 formal theorem statement，无法构建阶段提示词")

            # step1: construct_lemmas1 -> 解析引理并写入未证明库
            board.start(
                "construct_lemmas1",
                "提示词 %s ｜ 模型 %s"
                % (
                    Path(self.config.construct_lemmas1_prompt_path).name,
                    self.config.llm.model_name,
                ),
            )
            s1_sys, s1_tpl = self._load_prompt_template(self.config.construct_lemmas1_prompt_path)
            s1_user = self._fill_user_provide(
                s1_tpl,
                [func_block, theorem_block],
                self.config.construct_lemmas1_prompt_path,
            )
            s1_raw = self._call_stage_llm("step1_construct_lemmas1", s1_sys, s1_user)
            _s1_informal, s1_parsed = parse_construct_lemma_response(s1_raw)
            lemmas_stage1 = [x.get("statement", "").strip() for x in s1_parsed if (x.get("statement") or "").strip()]
            self.unproven_lemma_store.upsert_from_construct(
                lemmas_stage1,
                theorem_name,
                domain=domain,
                stage=SOURCE_GLOBAL,
                output_dir=self.config.output_dir,
            )
            s1_labels, s1_label_origin = self._linear_labels_from_parsed(s1_parsed)
            self._record_lemma_sources(
                lemmas_stage1,
                SOURCE_GLOBAL,
                linear_labels_by_name=s1_labels,
                linear_label_origin=s1_label_origin,
            )
            board.finish(
                "construct_lemmas1", note="候选引理 %d 条" % len(lemmas_stage1)
            )

            # step2: theorem statement -> informal proof
            board.start(
                "informal_proof",
                "提示词 %s" % Path(self.config.theorem_to_informal_prompt_path).name,
            )
            s2_sys, s2_tpl = self._load_prompt_template(self.config.theorem_to_informal_prompt_path)
            s2_user = self._fill_user_provide(
                s2_tpl,
                [func_block, theorem_block],
                self.config.theorem_to_informal_prompt_path,
            )
            s2_raw = self._call_stage_llm("step2_theorem_to_informal", s2_sys, s2_user)
            informal_proof = self._normalize_informal_proof(s2_raw)
            board.finish(
                "informal_proof",
                note="非形式化证明 %d 字符" % len(informal_proof),
            )

            # step3: construct_lemmas2 (依赖 step2 informal proof)
            board.start(
                "construct_lemmas2",
                "提示词 %s" % Path(self.config.construct_lemmas2_prompt_path).name,
            )
            s3_sys, s3_tpl = self._load_prompt_template(self.config.construct_lemmas2_prompt_path)
            s3_user = self._fill_user_provide(
                s3_tpl,
                [func_block, theorem_block, informal_proof],
                self.config.construct_lemmas2_prompt_path,
            )
            s3_raw = self._call_stage_llm("step3_construct_lemmas2", s3_sys, s3_user)
            _s3_informal, s3_parsed = parse_construct_lemma_response(s3_raw)
            lemmas_stage2 = [x.get("statement", "").strip() for x in s3_parsed if (x.get("statement") or "").strip()]
            self.unproven_lemma_store.upsert_from_construct(
                lemmas_stage2,
                theorem_name,
                domain=domain,
                stage=SOURCE_MIDDLE,
                output_dir=self.config.output_dir,
            )
            s3_labels, s3_label_origin = self._linear_labels_from_parsed(s3_parsed)
            self._record_lemma_sources(
                lemmas_stage2,
                SOURCE_MIDDLE,
                linear_labels_by_name=s3_labels,
                linear_label_origin=s3_label_origin,
            )
            board.finish(
                "construct_lemmas2", note="候选引理 %d 条" % len(lemmas_stage2)
            )

            # step4: informal proof -> formal proof（使用 step1+step3 合并引理）
            # 此时尚未生成 formal sketch，去重仅按引理文本/命题/名称
            # 参数阈值清单：生成 → 本批去重 → 补齐不变式 → 剔除引理库同名（实验漏斗）
            raw_candidates = list(lemmas_stage1) + list(lemmas_stage2)
            deduped_candidates, dedup_dropped = dedupe_lemma_statements_detailed(
                raw_candidates
            )
            augmented_candidates = ensure_pri_queue_invariant_lemmas(
                deduped_candidates,
                theorem_data,
            )
            _deduped_names = {
                extract_fact_name(_s) or "" for _s in deduped_candidates
            }
            invariant_added = sorted(
                _n
                for _n in (extract_fact_name(_s) or "" for _s in augmented_candidates)
                if _n and _n not in _deduped_names
            )
            _pre_filter_names = {
                extract_fact_name(_s) or "" for _s in augmented_candidates
            }
            combined_lemma_statements = ProvenLemmaStore.filter_lemmas_not_in_proven_library(
                augmented_candidates,
                self.config.output_dir,
                domain,
            )
            _kept_names = {
                extract_fact_name(_s) or "" for _s in combined_lemma_statements
            }
            name_conflict_dropped = sorted(
                _n for _n in _pre_filter_names if _n and _n not in _kept_names
            )
            result["lemma_funnel"] = {
                "stage1_count": len(lemmas_stage1),
                "stage3_count": len(lemmas_stage2),
                "raw_generated": len(raw_candidates),
                "after_dedup": len(deduped_candidates),
                "dedup_dropped_count": len(dedup_dropped),
                "dedup_dropped": dedup_dropped,
                "invariant_added": invariant_added,
                "after_name_filter": len(combined_lemma_statements),
                "name_conflict_dropped_count": len(name_conflict_dropped),
                "name_conflict_dropped": name_conflict_dropped,
            }
            self._record_fallback_linear_labels(combined_lemma_statements)
            s4_prompt_path = self.config.informal_to_formal_prompt_path
            board.start(
                "formal_sketch", "提示词 %s" % Path(s4_prompt_path).name
            )
            first_sketch, s4_raw = self._run_step4_formal_sketch(
                s4_prompt_path,
                func_block,
                theorem_block,
                informal_proof,
                available_lemmas=combined_lemma_statements,
            )
            board.finish(
                "formal_sketch", note="草图 %d 字符" % len(first_sketch or "")
            )

            parsed_concept_by_name: Dict[str, Dict[str, str]] = {}
            for _item in list(s1_parsed) + list(s3_parsed):
                _stmt = (_item.get("statement") or "").strip()
                _cname = extract_fact_name(_stmt)
                if not _cname:
                    continue
                _prev = parsed_concept_by_name.get(_cname)
                if _prev is None:
                    parsed_concept_by_name[_cname] = _item
                else:
                    for _key in ("meaning", "source", "linear_label"):
                        if not (_prev.get(_key) or "").strip() and (
                            _item.get(_key) or ""
                        ).strip():
                            _prev[_key] = _item[_key]

            constructed_lemma_concepts = [
                {
                    "name": f"constructed_lemma_{idx}",
                    "description": stmt,
                    "meaning": (
                        parsed_concept_by_name.get(
                            extract_fact_name(stmt or "") or "", {}
                        ).get("meaning")
                        or ""
                    ),
                    "source": (
                        parsed_concept_by_name.get(
                            extract_fact_name(stmt or "") or "", {}
                        ).get("source")
                        or "step1_or_step3"
                    ),
                    "linear_label": (
                        parsed_concept_by_name.get(
                            extract_fact_name(stmt or "") or "", {}
                        ).get("linear_label")
                        or ""
                    ),
                }
                for idx, stmt in enumerate(combined_lemma_statements, start=1)
            ]
            construct_lemma_raw = s1_raw
            construct_err: Optional[str] = None
            result["construct_lemma_raw"] = s1_raw
            result["constructed_lemma_statements"] = combined_lemma_statements
            result["step1_lemma_count"] = len(lemmas_stage1)
            result["step3_lemma_count"] = len(lemmas_stage2)
            result["lemmas_stage1"] = lemmas_stage1
            result["lemmas_stage3"] = lemmas_stage2
            result["informal_proof_raw"] = s2_raw
            result["formal_proof_raw"] = s4_raw

            run_artifact = TheoremRunArtifact(self.config.output_dir, theorem_name)
            run_artifact.write_after_construct(
                func_block,
                theorem_block,
                informal_proof,
                constructed_lemma_concepts,
                construct_lemma_raw,
                error=construct_err,
            )
            result["theorem_run_artifact"] = str(run_artifact.json_path)

            merged_lemma_concepts = self.sketch_generator.build_merged_lemma_concepts(
                theorem_data,
                informal_proof,
                constructed_lemma_concepts,
            )
            lemmas_block = self.sketch_generator.format_merged_lemmas_for_sketch(
                merged_lemma_concepts
            )
            run_artifact.update_merged_lemma_concepts(
                merged_lemma_concepts, lemmas_block
            )

            theory_dir = theorem_theory_dir(
                self.config.output_dir, domain, theorem_name
            )
            theory_dir.mkdir(parents=True, exist_ok=True)
            DefinitionStore.ensure_domain(self.config.output_dir, domain)
            DefinitionStore.merge_from_theorem_data(
                self.config.output_dir,
                domain,
                theorem_data,
                source_theorem=theorem_name,
                data_dir=self.config.data_dir,
            )
            ProvenLemmaStore.sync_to_theorem_dir(
                self.config.output_dir, theory_dir, domain
            )

            # 2) 在组装工作 .thy 之前，将未证明引理写入独立 .thy 文件
            unproven_thy_name = f"{theorem_name}_unproven_lemmas"
            unproven_thy_path = theory_dir / f"{unproven_thy_name}.thy"
            if combined_lemma_statements:
                from .lemma.unproven_lemma_store import UnprovenLemmaStore

                packages = theorem_data.get("packages", "Main")
                UnprovenLemmaStore.write_unproven_lemma_thy(
                    unproven_thy_path,
                    combined_lemma_statements,
                    unproven_thy_name,
                    packages=packages,
                    domain=domain,
                )
                print(
                    f"\n[unproven-lemmas] 独立引理 .thy: {unproven_thy_path}",
                    flush=True,
                )
                if (
                    self.config.lemmas_reflection_enabled
                    and self.isabelle_runner is not None
                ):
                    reflection = self.lemmas_reflection.reflect_until_valid(
                        unproven_thy_path=unproven_thy_path,
                        lemma_statements=combined_lemma_statements,
                        theorem_data=theorem_data,
                        informal_proof=informal_proof,
                        domain=domain,
                        packages=packages,
                        unproven_thy_name=unproven_thy_name,
                        isabelle_config=self.isabelle_runner,
                    )
                    combined_lemma_statements = reflection.lemma_statements
                    result["constructed_lemma_statements"] = combined_lemma_statements
                    result["lemmas_reflection"] = reflection.to_dict()
                    if not reflection.success:
                        from .lemma.lemmas_reflection import prune_invalid_lemma_statements

                        combined_lemma_statements = prune_invalid_lemma_statements(
                            combined_lemma_statements,
                            unproven_thy_path=unproven_thy_path,
                            unproven_thy_name=unproven_thy_name,
                            packages=packages,
                            domain=domain,
                            isabelle_config=self.isabelle_runner,
                            server_pool=None,
                        )
                        result["constructed_lemma_statements"] = combined_lemma_statements
                        logger.warning(
                            "引理反思未完全通过，已剪枝无效引理后继续（可能触发 sketch_repair）"
                        )
            else:
                if unproven_thy_path.exists():
                    unproven_thy_path.unlink()

            # 3) 生成 <定理>_sketch.thy 作为工作文件
            #    imports unproven（含定义+引理）；本文件仅含主定理草图
            sketch = first_sketch
            result["sketch"] = sketch
            result["status"] = "thy_generated"
            run_artifact.append_sketch(1, sketch)

            print("\n" + "="*80)
            print("📜 生成的证明草图 (Formal Sketch)")
            print("="*80)
            print(sketch if (sketch and sketch.strip()) else "(空)")
            print("="*80 + "\n")

            theory_file = self._create_sketch_theory(
                {**theorem_data, "theorem name": theorem_name},
                sketch,
                theory_dir,
                unproven_thy_name,
            )

            if theory_file and theory_file.exists():
                theory_content = theory_file.read_text(encoding="utf-8")
                print("\n" + "="*80)
                print(f"📄 工作理论文件 ({theory_file.name})")
                print("="*80)
                print(theory_content)
                print("="*80 + "\n")
                result["generated_theory_file"] = str(theory_file)

                need_isabelle_pool = bool(
                    self.isabelle_runner
                    and (
                        self.run_sledgehammer_after_thy
                        or (
                            self.config.lemma_quality_eval.enabled
                            and self.config.lemma_quality_eval.syntax_enabled
                        )
                    )
                )

                if need_isabelle_pool:
                    with IsabelleServerSessionPool(
                        self.isabelle_runner
                    ) as server_pool:
                        if self.run_sledgehammer_after_thy:
                            sketch, theory_file = self._run_sledgehammer_phase(
                                theorem_name,
                                theorem_data,
                                informal_proof,
                                combined_lemma_statements,
                                theory_dir,
                                theory_file,
                                sketch,
                                unproven_thy_path,
                                run_artifact,
                                result,
                                server_pool=server_pool,
                            )
                else:
                    if self.run_sledgehammer_after_thy and self.isabelle_runner:
                        logger.warning(
                            "未启用 Isabelle server 复用池，跳过 sledgehammer 阶段"
                        )

            # 5. 保存结果（包含 sledgehammer 回填后的理论文件）
            self._save_result(theorem_name, result, theorem_data, sketch, informal_proof, theory_file)
            
        except Exception as e:
            logger.error(f"证明过程出错: {e}", exc_info=True)
            result["error"] = str(e)
        
        return result
    
    def _run_sledgehammer_phase(
        self,
        theorem_name: str,
        theorem_data: Dict,
        informal_proof: str,
        combined_lemma_statements: List[str],
        theory_dir: Path,
        theory_file: Path,
        sketch: str,
        unproven_thy_path: Path,
        run_artifact: TheoremRunArtifact,
        result: Dict,
        *,
        server_pool: IsabelleServerSessionPool,
    ) -> Tuple[str, Path]:
        result_dir = Path(self.config.output_dir) / "results" / theorem_name
        board.start("sketch_verify", "sledgehammer 回填 + Isabelle 验证")
        if not (sketch or "").strip():
            # 空草图不能当作“验证通过”：否则最终会写出只有 theorem 声明、没有证明的文件。
            processed = {
                "thy_file": str(theory_file),
                "sanitized_before_verify": True,
                "success": False,
                "replaced_sledgehammer_count": 0,
                "failure_repair_count": 0,
                "verify_return_code": 1,
                "verify_output": "空草图：模型未返回主定理证明",
                "needs_llm_repair": True,
                "round_logs": [],
                "empty_sketch": True,
            }
            print(
                "[verify] 检测到空草图，跳过验证并进入草图修复",
                flush=True,
            )
        else:
            processed = process_sledgehammer_and_verify(
                str(theory_file),
                self.isabelle_runner,
                server_pool=server_pool,
            )
            print_thy_verify_result(processed)
        board.finish(
            "sketch_verify",
            ok=bool(processed.get("success")),
            note="sledgehammer 替换 %s 处"
            % processed.get("replaced_sledgehammer_count", 0),
        )

        # 论文 4.3：验证失败先做根因判定（引理缺失 vs 证明草图结构错误）
        failure_kind = ""
        if not processed.get("success"):
            error_text = processed.get("verify_output") or ""
            failure_kind = classify_verify_failure(error_text)
            result["verify_failure_kind"] = failure_kind
            result["verify_failure_rationale"] = failure_rationale(error_text)
            logger.info(
                "验证失败根因判定: %s（%s）",
                failure_kind,
                result["verify_failure_rationale"],
            )
            print(f"\n[failure-analysis] 根因判定: {failure_kind}", flush=True)

        repair_started = not processed.get("success")
        if repair_started:
            board.start("failure_repair", "Isabelle 验证未通过，进入修复")
        if processed.get("success") or failure_kind != MISSING_LEMMA:
            # 结构错误（或已成功）：回溯 2.2.1 修正草图
            repair_out = self.sketch_repair.run_repair_loop(
                SketchRepairLoopContext(
                    theorem_name=theorem_name,
                    theorem_data=theorem_data,
                    informal_proof=informal_proof,
                    combined_lemma_statements=combined_lemma_statements,
                    theory_dir=theory_dir,
                    result_dir=result_dir,
                    sketch=sketch,
                    theory_file=theory_file,
                    run_artifact=run_artifact,
                    isabelle_runner=self.isabelle_runner,
                    print_verify_result=print_thy_verify_result,
                    create_theory_file=self._create_sketch_theory,
                    server_pool=server_pool,
                ),
                processed,
            )
            sketch = repair_out.sketch
            theory_file = repair_out.theory_file or theory_file
            processed = repair_out.processed
            result["sketch_repair_attempts"] = repair_out.repair_attempts
            result["sketch_repair_history"] = repair_out.history
            result["sketch_repair_prompt_path"] = self.sketch_repair.prompt_path
        else:
            # 引理缺失：跳过草图修复，直接走 2.2.3 修复引理构造策略
            result.setdefault("sketch_repair_attempts", 0)
            result.setdefault("sketch_repair_history", [])

        result["sketch"] = sketch
        result["verification_result"] = processed
        result["sledgehammer_replaced_count"] = processed.get(
            "replaced_sledgehammer_count", 0
        )
        if not processed.get("success") and self.config.repair_lemma_enabled:
            processed = self._try_repair_lemma_after_failed_sketch(
                theorem_name=theorem_name,
                theorem_data=theorem_data,
                theory_dir=theory_dir,
                theory_file=theory_file,
                unproven_thy_path=unproven_thy_path,
                result_dir=result_dir,
                result=result,
                processed=processed,
                server_pool=server_pool,
            )
            result["verification_result"] = processed
        if repair_started:
            board.finish(
                "failure_repair",
                ok=bool(processed.get("success")),
                note="草图修复 %d 次 ｜ 修复引理构造 %s"
                % (
                    int(result.get("sketch_repair_attempts") or 0),
                    "启用" if result.get("repair_lemma_result") else "未启用",
                ),
            )
        if processed.get("success"):
            result["status"] = "thy_verified"
            if theory_file and theory_file.exists():
                usage_report = analyze_theorem_lemma_usage(
                    theory_file,
                    theorem_name,
                    combined_lemma_statements,
                    unproven_lemmas_path=unproven_thy_path,
                )
                usage_path = result_dir / "lemma_usage.json"
                usage_path.write_text(
                    json.dumps(
                        usage_report.to_dict(),
                        ensure_ascii=False,
                        indent=2,
                    ),
                    encoding="utf-8",
                )
                result["lemma_usage"] = usage_report.to_dict()
                result["lemma_usage_file"] = str(usage_path)
                n_external = len(usage_report.external_refs)
                all_unproven = usage_report.used + usage_report.unused
                n_to_prove = sum(1 for e in all_unproven if e.still_sorry)
                print(
                    f"\n[lemma-usage] proof 引用 unproven 引理 "
                    f"{len(usage_report.used)} 条，"
                    f"unproven 未引用 {len(usage_report.unused)} 条，"
                    f"unproven 待证合计 {n_to_prove} 条，"
                    f"外部引用 {n_external} 条（不迭代证明）",
                    flush=True,
                )
                lemmas_ready = True
                unproven_thy_name = f"{theorem_name}_unproven_lemmas"
                domain = theorem_data.get("domain", "priority_queue")
                if (
                    self.config.prove_used_lemmas_after_theorem
                    and self.isabelle_runner
                ):
                    board.start("lemma_proving", "待证引理 %d 条" % n_to_prove)
                    ul_result = prove_used_lemmas_after_theorem(
                        theory_file,
                        usage_report,
                        self.isabelle_runner,
                        self.lemma_proof_iterator,
                        self.lemma_cache,
                        unproven_lemmas_path=unproven_thy_path,
                        domain=domain,
                        server_pool=server_pool,
                    )
                    ul_path = result_dir / "used_lemma_proof.json"
                    ul_path.write_text(
                        json.dumps(
                            ul_result.to_dict(),
                            ensure_ascii=False,
                            indent=2,
                        ),
                        encoding="utf-8",
                    )
                    result["used_lemma_proof"] = ul_result.to_dict()
                    result["used_lemma_proof_file"] = str(ul_path)
                    lemmas_ready = ul_result.final_all_used_lemmas_verified
                    board.finish(
                        "lemma_proving",
                        ok=bool(lemmas_ready),
                        note="引理全部通过"
                        if lemmas_ready
                        else "仍有引理未通过（已恢复 sorry）",
                    )
                else:
                    board.skip(
                        "lemma_proving", "未启用（--no-prove-used-lemmas）"
                    )

                if lemmas_ready:
                    board.start("finalize", "生成自包含定理文件并验证")
                    if self._create_and_verify_final_theory(
                        theorem_name,
                        theorem_data,
                        theory_dir,
                        sketch,
                        result,
                        usage_report,
                        unproven_thy_name=unproven_thy_name,
                        server_pool=server_pool,
                        merge_proven_blocks=True,
                    ):
                        result["status"] = "theorem_and_used_lemmas_verified"
                    else:
                        result["status"] = "final_verification_failed"
                    board.finish(
                        "finalize",
                        ok=result["status"] == "theorem_and_used_lemmas_verified",
                        note="状态 %s" % result["status"],
                    )
                elif (
                    self.config.prove_used_lemmas_after_theorem
                    and self.isabelle_runner
                ):
                    result["status"] = "unproven_lemmas_incomplete"
                    board.skip("finalize", "引理未全部通过，未生成最终定理文件")
            if _theorem_verified(result):
                board.start("quality_eval", "定理成功后更新引理库质量")
                self._run_proven_lemma_library_quality_eval(
                    theorem_name,
                    theory_dir,
                    theorem_data.get("domain", "priority_queue"),
                    result,
                    server_pool=server_pool,
                )
                screening = result.get("quality_screening") or {}
                board.finish(
                    "quality_eval",
                    note="库内 %s 条 ｜ 淘汰 %s 条 ｜ 淘汰率 %s"
                    % (
                        screening.get("total", "-"),
                        screening.get("eliminated_count", "-"),
                        screening.get("elimination_rate", "-"),
                    ),
                )
            else:
                board.skip(
                    "quality_eval",
                    "定理未证明成功（%s），跳过质量评估与筛选"
                    % result.get("status"),
                )
        else:
            result["status"] = "thy_verification_failed"
        return sketch, theory_file

    def _try_repair_lemma_after_failed_sketch(
        self,
        *,
        theorem_name: str,
        theorem_data: Dict,
        theory_dir: Path,
        theory_file: Path,
        unproven_thy_path: Path,
        result_dir: Path,
        result: Dict,
        processed: Dict,
        server_pool: IsabelleServerSessionPool,
    ) -> Dict:
        """论文 2.3.3 / 4.3：草图验证失败时走修复引理构造 + 引理修正机制，再重试验证。"""
        ctx = RepairLemmaContext(
            theorem_name=theorem_name,
            theorem_data=theorem_data,
            theory_file=Path(theory_file),
            theory_dir=Path(theory_dir),
            result_dir=Path(result_dir),
            unproven_thy_path=Path(unproven_thy_path),
            verify_output=processed.get("verify_output") or "",
            repair_prompt_path=self.config.repair_lemma_prompt_path,
            revision_prompt_path=self.config.lemma_revision_prompt_path,
            max_attempts=self.config.max_repair_lemma_attempts,
        )
        last: Dict[str, Dict] = {"processed": processed}

        def _reverify() -> Tuple[bool, str]:
            re_processed = process_sledgehammer_and_verify(
                str(theory_file), self.isabelle_runner, server_pool=server_pool
            )
            print_thy_verify_result(re_processed)
            last["processed"] = re_processed
            return (
                bool(re_processed.get("success")),
                re_processed.get("verify_output") or "",
            )

        try:
            repair_out = self.repair_lemma.run_loop(ctx, verify_callback=_reverify)
        except Exception as exc:
            logger.error("修复引理构造失败: %s", exc, exc_info=True)
            result["repair_lemma_error"] = str(exc)
            return processed

        result["repair_lemma_result"] = {
            "success": repair_out.success,
            "attempts": repair_out.attempts,
            "marker_line": repair_out.marker_line,
            "merged_names": repair_out.merged_names,
            "linear_labels": dict(getattr(repair_out, "linear_labels", None) or {}),
            "history": repair_out.history,
        }
        if repair_out.merged_names:
            # 论文 3.2.1(1)：修复引理构造策略产出的引理标记为 repair
            repair_mapping: Dict[str, dict] = {
                n: {"source": SOURCE_REPAIR} for n in repair_out.merged_names
            }
            # 方案 C：优先采用模型在修复提示词中给出的 Linear label；
            # 模型未给出（或无法规范化）时回退到陈述正则，来源写入 linear_label_source。
            _model_labels = getattr(repair_out, "linear_labels", None) or {}
            try:
                from .eval.proof_difficulty_score_v2.thy_extract import (
                    extract_decl_blocks,
                )

                _blocks = extract_decl_blocks(
                    Path(unproven_thy_path).read_text(encoding="utf-8")
                )
                _statements_by_name = {
                    extract_fact_name(b): b for b in _blocks if extract_fact_name(b)
                }
            except Exception as exc:
                logger.warning("修复引理陈述解析失败: %s", exc)
                _statements_by_name = {}
            for _n in repair_out.merged_names:
                _labels = canonicalize_linear_labels(_model_labels.get(_n) or "")
                if _labels:
                    repair_mapping[_n]["linear_labels"] = _labels
                    repair_mapping[_n]["linear_label_source"] = "llm"
                else:
                    _block = _statements_by_name.get(_n)
                    if _block:
                        repair_mapping[_n]["linear_labels"] = (
                            identify_linear_labels(_block)
                        )
                        repair_mapping[_n]["linear_label_source"] = (
                            "statement_fallback"
                        )
            record_labels(self.config.output_dir, repair_mapping)
        if repair_out.success:
            return last["processed"]
        return processed

    @staticmethod
    def _linear_labels_from_parsed(
        parsed: List[Dict[str, str]],
    ) -> Tuple[Dict[str, List[str]], Dict[str, str]]:
        """方案 C：优先采用模型给出的 Linear label（规范化后），无法识别时回退到陈述正则。"""
        labels_by_name: Dict[str, List[str]] = {}
        origin_by_name: Dict[str, str] = {}
        for item in parsed or []:
            stmt = (item.get("statement") or "").strip()
            name = extract_fact_name(stmt)
            if not name:
                continue
            labels = canonicalize_linear_labels(item.get("linear_label") or "")
            if labels:
                origin_by_name[name] = "llm"
            else:
                labels = identify_linear_labels(stmt)
                origin_by_name[name] = "statement_fallback"
            labels_by_name[name] = labels
        return labels_by_name, origin_by_name

    def _record_fallback_linear_labels(self, statements: List[str]) -> None:
        """为引擎补充引理（未经过模型标注）补齐线性标签：正则回退，来源可追溯。"""
        existing = load_labels(self.config.output_dir)
        mapping: Dict[str, dict] = {}
        for stmt in statements or []:
            name = extract_fact_name(stmt or "")
            if not name:
                continue
            entry = existing.get(name) or {}
            if entry.get("linear_labels"):
                continue
            mapping[name] = {
                "linear_labels": identify_linear_labels(stmt),
                "linear_label_source": "statement_fallback",
            }
        if mapping:
            record_labels(self.config.output_dir, mapping)

    def _record_lemma_sources(
        self,
        statements: List[str],
        source: str,
        linear_labels_by_name: Optional[Dict[str, List[str]]] = None,
        linear_label_origin: Optional[Dict[str, str]] = None,
    ) -> None:
        """论文 3.2.1：记录来源标签（global/middle/repair）与线性标签（方案 C）。"""
        from .utils.lemma_dedup import extract_fact_name

        mapping: Dict[str, dict] = {}
        for stmt in statements or []:
            name = extract_fact_name(stmt or "")
            if name:
                mapping[name] = {"source": source}
        for name, labels in (linear_labels_by_name or {}).items():
            if name in mapping and labels:
                mapping[name]["linear_labels"] = list(labels)
                origin = (linear_label_origin or {}).get(name)
                if origin:
                    mapping[name]["linear_label_source"] = origin
        if mapping:
            record_labels(self.config.output_dir, mapping)

    def _run_proven_lemma_library_quality_eval(
        self,
        theorem_name: str,
        theory_dir: Path,
        domain: str,
        result: Dict,
        *,
        server_pool: Optional[IsabelleServerSessionPool] = None,
        advance_batch: bool = True,
    ) -> None:
        """定理验证成功后，对领域 proven_lemmas.thy 中全部引理做质量评估。"""
        if not _theorem_verified(result):
            # 论文 4.1.2 主口径：复用率只统计「证明成功的定理」的引用；
            # 定理未证明成功时不做评估与筛选，避免把失败定理的引用写进引理库。
            logger.info(
                "定理未证明成功（status=%s），跳过引理库质量评估与筛选",
                result.get("status"),
            )
            return
        if not self.config.lemma_quality_eval.enabled:
            return
        if not (
            self.config.lemma_quality_eval.syntax_enabled
            or self.config.lemma_quality_eval.proof_difficulty_v2_enabled
        ):
            return
        try:
            local_proven = ProvenLemmaStore.sync_to_theorem_dir(
                self.config.output_dir, theory_dir, domain
            )
            evaluator = LemmaQualityEvaluator(
                config=self.config.lemma_quality_eval,
                llm=self.llm,
            )
            report = evaluator.evaluate_proven_lemma_library(
                local_proven,
                triggered_by_theorem=theorem_name,
                server_pool=server_pool,
            )
            global_dir = Path(self.config.output_dir) / "results" / "proven_lemmas"
            global_dir.mkdir(parents=True, exist_ok=True)
            report_path = global_dir / "lemma_quality_latest.json"
            LemmaQualityEvaluator.save_report(report, report_path)
            theorem_result_dir = (
                Path(self.config.output_dir) / "results" / theorem_name
            )
            theorem_report_path = theorem_result_dir / "proven_lemma_library_quality.json"
            LemmaQualityEvaluator.save_report(report, theorem_report_path)
            evaluator.print_proven_library_summary(report)
            syntax_results, _report_difficulty = (
                LemmaQualityEvaluator.extract_score_inputs_from_proven_report(
                    report
                )
            )
            # 论文 3.1.1/3.1.2：D(i) 用依赖闭包、U(i) 用库内直接调用者（不沿链上溯）
            dependency_analysis: Dict[str, Dict] = {}
            dep_d: Dict[str, int] = {}
            dep_u: Dict[str, int] = {}
            dependency_file = global_dir / "dependency_graph.json"
            global_thy_path = ProvenLemmaStore.global_thy_path(
                self.config.output_dir, domain
            )
            # 定理级引用以验证通过的最终定理理论文本为准（回退到草图）
            theorem_proof_texts: List[str] = []
            proof_sources: List[Path] = [
                Path(theory_dir) / f"{theorem_name}.thy"
            ]
            final_theory_file = result.get("final_theory_file")
            if final_theory_file:
                proof_sources.append(Path(final_theory_file))
            for proof_src in proof_sources:
                if proof_src.is_file():
                    theorem_proof_texts.append(
                        proof_src.read_text(encoding="utf-8")
                    )
                    break
            if not theorem_proof_texts:
                theorem_proof_texts.append(str(result.get("sketch") or ""))
            try:
                from .eval.dependency_graph import analyze_thy_text

                if global_thy_path.is_file():
                    dependency_analysis = analyze_thy_text(
                        global_thy_path.read_text(encoding="utf-8"),
                        theorem_texts=theorem_proof_texts,
                    )
                    dep_d = {n: int(v["d"]) for n, v in dependency_analysis.items()}
                    dep_u = {n: int(v["u"]) for n, v in dependency_analysis.items()}
                    dependency_file.write_text(
                        json.dumps(
                            dependency_analysis, ensure_ascii=False, indent=2
                        ),
                        encoding="utf-8",
                    )
            except Exception as dep_exc:
                logger.warning("依赖图计算失败: %s", dep_exc)

            scores: Dict[str, dict] = {}
            if syntax_results or dep_d or dep_u:
                scores = ProvenLemmaStore.compute_and_save_quality_scores(
                    self.config.output_dir,
                    domain,
                    syntax_results=syntax_results or None,
                    proof_difficulty_results=dep_d or None,
                    reuse_counts=dep_u or None,
                )
            result["dependency_graph"] = dependency_analysis
            result["dependency_graph_file"] = str(dependency_file)
            # 论文 3.2：质量筛选——来源/线性标签、差异化衰减与阈值淘汰
            try:
                from .eval.proof_difficulty_score_v2.thy_extract import (
                    extract_decl_blocks,
                )

                library_scores = scores or ProvenLemmaStore.load_quality_scores(
                    self.config.output_dir
                )
                label_data = load_labels(self.config.output_dir)
                global_thy_text = (
                    global_thy_path.read_text(encoding="utf-8")
                    if global_thy_path.is_file()
                    else ""
                )
                statements = extract_decl_blocks(global_thy_text)
                outcome = screen_batch(
                    library_scores,
                    source_by_lemma=source_map_from_labels(label_data),
                    linear_by_lemma=linear_map_from_labels(label_data),
                    statements=statements,
                    direct_dependencies={
                        name: list(info.get("direct") or [])
                        for name, info in dependency_analysis.items()
                    },
                    previous_q=load_state(self.config.output_dir),
                    base=self.config.paper.decay_base,
                    q_min=self.config.paper.q_min,
                    source_coefficients=self.config.paper.source_coefficient,
                    linear_coefficients=self.config.paper.linear_coefficient,
                )
                screening_file = global_dir / "quality_screening.json"
                screening_file.write_text(
                    json.dumps(outcome.to_dict(), ensure_ascii=False, indent=2),
                    encoding="utf-8",
                )
                if outcome.removed:
                    ProvenLemmaStore.remove_lemma_blocks_from_thy(
                        global_thy_path, outcome.removed
                    )
                ProvenLemmaStore.save_quality_scores(
                    self.config.output_dir, outcome.updated
                )
                save_state(
                    self.config.output_dir,
                    {n: row["q"] for n, row in outcome.updated.items()},
                )
                # 论文 3.2.1 / 第 5 章实验指标：按来源与线性标签分类归档
                from .eval.lemma_classification import update_classification

                defs_path = Path(theory_dir).parent / "defs.thy"
                definitions_block = ""
                if defs_path.is_file():
                    definitions_block = ProvenLemmaStore.extract_definitions_preamble(
                        defs_path.read_text(encoding="utf-8")
                    )
                if not definitions_block.strip():
                    definitions_block = ProvenLemmaStore.extract_definitions_preamble(
                        global_thy_text
                    )
                classification_dir = update_classification(
                    self.config.output_dir,
                    domain=domain,
                    theorem_name=theorem_name,
                    scores=outcome.updated,
                    labels=label_data,
                    statements=statements,
                    eliminated=outcome.removed,
                    lemma_blocks=statements,
                    block_order=list(statements.keys()),
                    definitions_block=definitions_block,
                )
                result["lemma_classification_dir"] = str(classification_dir)
                result["lemma_classification_thy_files"] = [
                    str(p) for p in sorted(classification_dir.rglob("*_lemmas.thy"))
                ]
                result["quality_screening"] = outcome.to_dict()
                result["quality_screening_file"] = str(screening_file)
                # 论文 2.4 / 3.1 / 3.2 / 4.1.2：引理库总览
                # （陈述、证明、被调用次数、存活周期、引理质量）
                from .eval.lemma_library import record_batch_and_export

                library_path = record_batch_and_export(
                    self.config.output_dir,
                    domain=domain,
                    theorem_name=theorem_name,
                    paper=self.config.paper,
                    advance_batch=advance_batch,
                )
                result["lemma_library_file"] = str(library_path)
            except Exception as screen_exc:
                logger.warning("引理质量筛选失败: %s", screen_exc)
                result["quality_screening_error"] = str(screen_exc)
            result["proven_lemma_library_quality"] = report.to_dict()
            result["proven_lemma_library_quality_file"] = str(report_path)
            result["proven_lemma_library_quality_theorem_file"] = str(
                theorem_report_path
            )
        except Exception as eval_exc:
            logger.warning("全局已证引理库质量评估失败: %s", eval_exc)
            result["proven_lemma_library_quality_error"] = str(eval_exc)

    def _finalize_after_lemma_proving(
        self,
        theorem_name: str,
        theorem_data: Dict,
        theory_dir: Path,
        usage_report: TheoremLemmaUsageReport,
        sketch: str,
        result: Dict,
        *,
        unproven_thy_name: str,
        domain: str,
        server_pool: Optional[IsabelleServerSessionPool] = None,
    ) -> None:
        """
        引理迭代证明全部通过后的收尾：
        1) 将 unproven 中全部已证引理合并进领域 proven_lemmas.thy
        2) 将遗留定义合并进同领域 defs.thy
        3) 从 unproven 中移除已迁入库的引理块
        4) 生成最终 <定理>.thy（imports Main ../<domain>/defs ../<domain>/proven_lemmas）
        """
        from .lemma_proving.iterator import lemma_block_text
        from .lemma_proving.usage import lemma_blocks_in_thy, lemma_still_sorry

        unproven_thy_path = theory_dir / f"{unproven_thy_name}.thy"
        unproven_text = unproven_thy_path.read_text(encoding="utf-8")
        unproven_blocks = lemma_blocks_in_thy(unproven_text)
        defs_block = ProvenLemmaStore.extract_definitions_preamble(unproven_text)
        if defs_block.strip():
            DefinitionStore.merge_definitions_block(
                self.config.output_dir,
                domain,
                defs_block,
                source_theorem=theorem_name,
            )
        sketch_text = sketch
        sketch_thy = theory_dir / f"{theorem_name}_sketch.thy"
        if sketch_thy.is_file():
            sketch_text = sketch_thy.read_text(encoding="utf-8")

        proven_blocks: List[str] = []
        merged_names: List[str] = []
        for name in sorted(unproven_blocks.keys()):
            block = lemma_block_text(unproven_text, name) or unproven_blocks[name]
            if lemma_still_sorry(block):
                logger.warning(
                    "finalize: unproven 引理 %s 仍为 sorry，跳过合并",
                    name,
                )
                continue
            proven_blocks.append(block)
            merged_names.append(name)

        global_path = ProvenLemmaStore.proven_thy_path(self.config.output_dir, domain)
        proven_backup: Optional[str] = None
        if global_path.is_file():
            proven_backup = global_path.read_text(encoding="utf-8")

        from .utils.lemma_dedup import rewrite_lemma_names_in_text

        def _failed_lemma_names(thy_path: Path, verify_output: str) -> set[str]:
            from .utils.isabelle_sledgehammer import _extract_error_positions

            try:
                thy_text = thy_path.read_text(encoding="utf-8")
            except OSError:
                return set()
            lines = thy_text.splitlines()
            names: set[str] = set()
            for line_no, _msg in _extract_error_positions(verify_output or ""):
                if not (1 <= line_no <= len(lines)):
                    continue
                for idx in range(line_no - 1, -1, -1):
                    match = re.match(
                        r"\s*(?:lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)",
                        lines[idx],
                    )
                    if match:
                        names.add(match.group(1))
                        break
            return names

        defs_path = DefinitionStore.defs_thy_path(self.config.output_dir, domain)
        current_blocks = list(proven_blocks)
        merge_verified = True
        merge_verify_out = ""
        n_merged = 0
        merge_alias_map: Dict[str, str] = {}
        for merge_attempt in range(1, 4):
            if merge_attempt > 1:
                if proven_backup is not None:
                    global_path.write_text(proven_backup, encoding="utf-8")
                elif global_path.is_file():
                    global_path.unlink()

            n_merged, merge_alias_map = ProvenLemmaStore.merge_proven_blocks(
                self.config.output_dir,
                domain,
                current_blocks,
                source_theorem=theorem_name,
                definitions_block=defs_block,
                similarity_threshold=self.config.lemma_cache.similarity_threshold,
                local_lemma_names=sorted(unproven_blocks.keys()),
            )
            if merge_alias_map:
                sketch_text = rewrite_lemma_names_in_text(sketch_text, merge_alias_map)
                if sketch_thy.is_file():
                    sketch_thy.write_text(
                        rewrite_lemma_names_in_text(
                            sketch_thy.read_text(encoding="utf-8"),
                            merge_alias_map,
                        ),
                        encoding="utf-8",
                    )
                result["proven_merge_lemma_aliases"] = merge_alias_map
            merge_verified = True
            if n_merged == 0 or not self.isabelle_runner:
                break

            from .utils.isabelle_sledgehammer import verify_domain_proven_lemmas_after_merge

            merge_verified, merge_verify_out = verify_domain_proven_lemmas_after_merge(
                global_path,
                defs_path,
                self.isabelle_runner,
                server_pool,
            )
            if merge_verified:
                break

            failed_names = _failed_lemma_names(global_path, merge_verify_out)
            remaining = [
                block
                for block in current_blocks
                if (extract_fact_name(block) or "") not in failed_names
            ]
            if not failed_names or len(remaining) == len(current_blocks):
                break
            logger.warning(
                "proven merge verification failed; dropping non-reusable lemmas and retrying: %s",
                ", ".join(sorted(failed_names)),
            )
            result.setdefault("proven_merge_dropped_lemmas", []).extend(
                sorted(failed_names)
            )
            merged_names = [name for name in merged_names if name not in failed_names]
            current_blocks = remaining

        if not merge_verified:
            if proven_backup is not None:
                global_path.write_text(proven_backup, encoding="utf-8")
            elif global_path.is_file():
                global_path.unlink()
            logger.error(
                "proven merge verification failed after retries; rolled back %s",
                global_path,
            )
            result["proven_merge_verification_failed"] = True
            merged_names = []
            n_merged = 0

        ProvenLemmaStore.sync_to_theorem_dir(
            self.config.output_dir, theory_dir, domain
        )
        from .utils.isabelle_sledgehammer import _mark_thy_disk_changed

        _mark_thy_disk_changed(server_pool)
        if merge_verified and merged_names:
            ProvenLemmaStore.remove_lemma_blocks_from_thy(
                unproven_thy_path, merged_names
            )
        print(
            f"\n[proven-lemmas] 领域 {domain} 已证引理库: {global_path}"
            f"（本次合并 {n_merged} 条，库内共 {len(ProvenLemmaStore.list_lemma_blocks(self.config.output_dir, domain))} 条）",
            flush=True,
        )

        final_thy = self._create_final_theory(
            {**theorem_data, "theorem name": theorem_name},
            sketch_text,
            theory_dir,
        )
        print(
            f"\n[final-theory] 最终理论文件: {final_thy}",
            flush=True,
        )
        result["final_theory_file"] = str(final_thy)
        result["proven_lemmas_file"] = str(global_path)

    def _create_and_verify_final_theory(
        self,
        theorem_name: str,
        theorem_data: Dict,
        theory_dir: Path,
        sketch: str,
        result: Dict,
        usage_report: Optional[TheoremLemmaUsageReport],
        *,
        unproven_thy_name: str,
        server_pool: Optional[IsabelleServerSessionPool] = None,
        merge_proven_blocks: bool = True,
    ) -> bool:
        """
        生成最终 <定理>.thy（imports Main proven_lemmas，不含 unproven），
        并在该文件上执行 Isabelle 验证；通过后才写入 verified/。
        """
        if merge_proven_blocks and usage_report is not None:
            self._finalize_after_lemma_proving(
                theorem_name,
                theorem_data,
                theory_dir,
                usage_report,
                sketch,
                result,
                unproven_thy_name=unproven_thy_name,
                domain=theorem_data.get("domain", "priority_queue"),
                server_pool=server_pool,
            )
            if result.get("proven_merge_verification_failed"):
                logger.error("proven merge 后全量验证失败，跳过 final 验证")
                return False
        else:
            sketch_text = sketch
            sketch_thy = theory_dir / f"{theorem_name}_sketch.thy"
            if sketch_thy.is_file():
                sketch_text = sketch_thy.read_text(encoding="utf-8")
            final_thy = self._create_final_theory(
                {**theorem_data, "theorem name": theorem_name},
                sketch_text,
                theory_dir,
            )
            print(
                f"\n[final-theory] 最终理论文件: {final_thy}",
                flush=True,
            )
            result["final_theory_file"] = str(final_thy)

        final_path = Path(result.get("final_theory_file") or "")
        if not final_path.is_file():
            logger.error("最终理论文件未生成: %s", final_path)
            return False

        domain = theorem_data.get("domain", "priority_queue")
        if self.isabelle_runner and server_pool and server_pool.is_active:
            # 自包含定理：干净 session 验证（不预载自定义引理库）
            prepare_session_for_self_contained_verify(
                self.isabelle_runner,
                server_pool,
            )

        processed = process_sledgehammer_and_verify(
            str(final_path),
            self.isabelle_runner,
            server_pool=server_pool,
        )
        print_thy_verify_result(processed)
        result["verification_result"] = processed
        result["final_theorem_verified"] = bool(processed.get("success"))
        return result["final_theorem_verified"]
    
    def prove_batch(self, data_dir: str, count: Optional[int] = None) -> List[Dict]:
        """
        批量证明定理
        
        Args:
            data_dir: 数据目录
            count: 处理数量限制
            
        Returns:
            List[Dict]: 结果列表
        """
        data_path = Path(data_dir)
        theorem_files = list(data_path.glob("*.json"))
        
        if count:
            theorem_files = theorem_files[:count]
        
        results = []
        batch_start = time.perf_counter()
        total = len(theorem_files)
        for i, theorem_file in enumerate(theorem_files, 1):
            logger.info(f"处理 {i}/{len(theorem_files)}: {theorem_file.name}")
            print("")
            print("=" * 78)
            print("[定理 %d/%d] %s" % (i, total, theorem_file.name))
            print("=" * 78, flush=True)
            result = self.prove_theorem(str(theorem_file))
            result["_batch_index"] = i
            results.append(result)
            print(
                "[定理 %d/%d] 结果：%s"
                % (i, total, result.get("status") or "unknown"),
                flush=True,
            )

        # 生成摘要报告
        self._generate_summary(results)
        self._print_batch_board(results, time.perf_counter() - batch_start)

        return results

    def _print_batch_board(self, results: List[Dict], elapsed: float) -> None:
        """批量跑分汇总表（逐条状态 + 总耗时）。"""
        total = len(results)
        success = sum(
            1 for r in results if self._theorem_attempt_succeeded(r)
        )
        print("")
        print("=" * 78)
        print(
            " 批量汇总 ｜ 共 %d 条 ｜ 成功 %d 条 ｜ 失败 %d 条 ｜ 总耗时 %s"
            % (total, success, total - success, format_duration(elapsed))
        )
        print("-" * 78)
        for idx, r in enumerate(results, 1):
            name = r.get("theorem_name") or "unknown"
            status = r.get("status") or "unknown"
            mark = "✓" if self._theorem_attempt_succeeded(r) else "✗"
            print(" %s %2d. %-42s %s" % (mark, idx, name, status))
        print("=" * 78)
    
    def _load_theorem_data(self, theorem_file: str) -> Dict:
        """加载定理数据，并补充同领域其他数据文件的定义（只增不减）。"""
        with open(theorem_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        try:
            domain = resolve_domain(data, theorem_file)
        except Exception:
            return data
        data.setdefault("domain", domain)
        data_dir = getattr(self.config, "data_dir", None)
        if data_dir:
            from .lemma.definition_store import DefinitionStore

            block = DefinitionStore.collect_domain_definitions(
                data_dir, domain, exclude_theorem=Path(theorem_file).stem
            )
            if block.strip():
                data["domain definitions"] = block
        return data
    
    def _create_sketch_theory(
        self,
        theorem_data: Dict,
        sketch: str,
        output_dir: Path,
        unproven_thy_name: str,
    ) -> Path:
        """
        生成 <定理>_sketch.thy：
        imports Main ../defs ../proven_lemmas "<定理>_unproven_lemmas"；本文件仅含主定理草图。
        """
        theorem_name = theorem_data.get("theorem name", "theorem")
        packages = theorem_data.get("packages", "Main")
        domain = theorem_data.get("domain")
        if not domain:
            raise ValueError(
                "theorem_data 缺少 domain；请由 prove_theorem 从 JSON 路径解析并注入"
            )

        imports_line = theorem_sketch_imports(
            packages=packages,
            domain=domain,
            unproven_thy_name=unproven_thy_name,
        )
        theory_name = f"{theorem_name}_sketch"

        content = f"""theory "{theory_name}"
imports {imports_line}
begin

declare [[quick_and_dirty = true]]

"""
        sketch_body = merge_sketch_into_theory(sketch, theorem_name, set())
        # 论文 2.2.2/图 2-4：草图层可能只给证明体；补形式化定理陈述并纠正被改写的定理名
        sketch_body = ensure_main_theorem_declaration(
            sketch_body,
            theorem_data.get("formal theorem statement") or "",
            theorem_name,
        )
        if sketch_body:
            content += sketch_body
            if not content.endswith("\n"):
                content += "\n"
        content += "\nend\n"
        content = truncate_theory_to_first_closure(content)

        thy_path = output_dir / f"{theory_name}.thy"
        thy_path.write_text(content, encoding="utf-8")
        return thy_path

    def _create_final_theory(
        self,
        theorem_data: Dict,
        sketch: str,
        output_dir: Path,
    ) -> Path:
        """
        生成 <定理>.thy（最终成品，自包含）：
        imports Main；文件内含领域定义 + 定理直接/间接引用的库内引理 + 主定理证明。
        不导入 ../defs 与 ../proven_lemmas，使定理不受引理库增删影响。
        """
        theorem_name = theorem_data.get("theorem name", "theorem")
        packages = theorem_data.get("packages", "Main")
        domain = theorem_data.get("domain")
        if not domain:
            raise ValueError(
                "theorem_data 缺少 domain；请由 prove_theorem 从 JSON 路径解析并注入"
            )

        imports_line = theorem_self_contained_imports(packages=packages)

        sketch_body = merge_sketch_into_theory(sketch, theorem_name, set())
        sketch_body = ensure_main_theorem_declaration(
            sketch_body,
            theorem_data.get("formal theorem statement") or "",
            theorem_name,
        )
        sketch_body = strip_quick_and_dirty_declarations(sketch_body)

        defs_text = strip_quick_and_dirty_declarations(
            DefinitionStore.read_definitions(self.config.output_dir, domain)
        ).strip()
        referenced_blocks = ProvenLemmaStore.referenced_lemma_blocks(
            self.config.output_dir, domain, sketch_body
        )
        # 与主定理同名的引理不能内联：Isabelle 不允许 lemma/theorem 重名。
        referenced_blocks = [
            block
            for block in referenced_blocks
            if (_declared_name(block) or "") != str(theorem_name)
        ]

        parts: List[str] = [
            f'theory "{theorem_name}"',
            f"imports {imports_line}",
            "begin",
            "",
        ]
        if defs_text:
            parts.extend([defs_text, ""])
        for block in referenced_blocks:
            parts.extend([block.strip(), ""])
        if sketch_body.strip():
            parts.extend([sketch_body.strip(), ""])
        parts.append("end")
        content = "\n".join(parts) + "\n"
        content = truncate_theory_to_first_closure(content)

        thy_path = output_dir / f"{theorem_name}.thy"
        thy_path.write_text(content, encoding="utf-8")
        return thy_path
    
    def _save_result(
        self,
        theorem_name: str,
        result: Dict,
        theorem_data: Dict,
        sketch: str,
        informal_proof: Optional[str],
        theory_file: Optional[Path]
    ):
        """
        保存结果到文件（类似prover_library的结构）
        
        Args:
            theorem_name: 定理名称
            result: 结果字典
            theorem_data: 定理数据
            sketch: 证明草图
            informal_proof: 非形式化证明（可选）
            theory_file: 理论文件路径（可选）
        """
        # 保存到results目录
        result_dir = Path(self.config.output_dir) / "results" / theorem_name
        result_dir.mkdir(parents=True, exist_ok=True)
        
        # 保存非形式化证明
        if informal_proof:
            informal_file = result_dir / "informal_proof.txt"
            informal_file.write_text(informal_proof, encoding='utf-8')

        raw_cl = result.get("construct_lemma_raw")
        if raw_cl:
            (result_dir / "construct_lemma_response.txt").write_text(
                raw_cl, encoding="utf-8"
            )
        stmts = result.get("constructed_lemma_statements")
        if stmts:
            (result_dir / "constructed_lemmas.json").write_text(
                json.dumps(stmts, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
        
        # 保存形式化草图
        sketch_file = result_dir / "formal_sketch.txt"
        sketch_file.write_text(sketch, encoding='utf-8')
        
        # 保存理论文件（优先最终 .thy，否则工作 sketch .thy）
        thy_for_results = theory_file
        final_path = result.get("final_theory_file")
        if final_path and Path(final_path).is_file():
            thy_for_results = Path(final_path)
        if thy_for_results and thy_for_results.exists():
            theory_content = thy_for_results.read_text(encoding="utf-8")
            result_thy_file = result_dir / f"{theorem_name}.thy"
            result_thy_file.write_text(theory_content, encoding='utf-8')
        
        # 保存生成漏斗（四层过滤）供实验统计
        funnel_file = result_dir / "lemma_funnel.json"
        funnel_file.write_text(
            json.dumps(
                result.get("lemma_funnel") or {}, ensure_ascii=False, indent=2
            ),
            encoding="utf-8",
        )

        # 保存JSON结果
        result_file = result_dir / "result.json"
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)
        
        # 如果最终 .thy 验证成功，额外保存到 verified 目录（不使用 sketch 工作文件）
        if result.get("status") == "theorem_and_used_lemmas_verified":
            final_path = result.get("final_theory_file")
            thy_for_verified = Path(final_path) if final_path else None
            if thy_for_verified and thy_for_verified.is_file():
                verified_dir = Path(self.config.output_dir) / "verified" / theorem_name
                verified_dir.mkdir(parents=True, exist_ok=True)

                verified_thy_file = verified_dir / f"{theorem_name}.thy"
                theory_content = thy_for_verified.read_text(encoding="utf-8")

                # 归档自洽化：复制依赖的 defs.thy / proven_lemmas.thy 到归档目录，
                # 并把定理 .thy 中 "../defs" / "../proven_lemmas" 等上级引用重写为
                # 同目录引用，使归档副本可就地通过 Isabelle 验证。
                proven_global_path = result.get("proven_lemmas_file")
                archive_dep_names: list[str] = []
                if proven_global_path:
                    proven_global = Path(proven_global_path)
                    domain_theory_dir = proven_global.parent
                    for dep_name in ("defs", "proven_lemmas"):
                        dep_src = domain_theory_dir / f"{dep_name}.thy"
                        if dep_src.is_file():
                            dep_dst = verified_dir / f"{dep_name}.thy"
                            dep_dst.write_text(
                                dep_src.read_text(encoding="utf-8"),
                                encoding="utf-8",
                            )
                            archive_dep_names.append(dep_name)
                for dep_name in archive_dep_names:
                    theory_content = re.sub(
                        rf'"\.\./{re.escape(dep_name)}"',
                        f'"{dep_name}"',
                        theory_content,
                    )

                verified_thy_file.write_text(theory_content, encoding='utf-8')

                verification_info = result.get("verification_result") or {}
                if not isinstance(verification_info, dict):
                    verification_info = {}
                formal_statement = (
                    theorem_data.get("formal_statement")
                    or theorem_data.get("theorem statement")
                    or theorem_data.get("statement")
                    or "（未提供）"
                )

                proof_summary = f"""# 验证成功的证明: {theorem_name}

## 定理陈述
{formal_statement}

## 非形式化证明
{informal_proof if informal_proof else "（未提供）"}

## 形式化证明草图
```isabelle
{sketch}
```

## 最终理论文件
```isabelle
{theory_content}
```

## 验证信息
- 成功: {verification_info.get('success', False)}
- 验证文件: {thy_for_verified.name}

"""

                summary_file = verified_dir / "proof_summary.md"
                summary_file.write_text(proof_summary, encoding='utf-8')

                print(f"\n{'='*60}")
                print(f"[OK] 验证成功! 结果已保存到以下位置:")
                print(f"{'='*60}")
                print(f"\n结果目录 (results/):")
                print(f"  - {result_dir}")
                print(f"    - formal_sketch.txt")
                if informal_proof:
                    print(f"    - informal_proof.txt")
                print(f"    - {theorem_name}.thy")
                print(f"    - result.json")

                print(f"\n验证目录 (verified/):")
                print(f"  - {verified_dir}")
                print(f"    - {theorem_name}.thy")
                print(f"    - proof_summary.md")

                print(f"\n理论文件目录 (theory/):")
                print(f"  - {thy_for_verified.parent}")
                print(f"    - {thy_for_verified.name}")
                self._build_delivery_bundle(
                    theorem_name, result, theorem_data
                )
                proven_global = result.get("proven_lemmas_file")
                if proven_global:
                    print(f"\n全局已证引理库:")
                    print(f"  - {proven_global}")

                print(f"{'='*60}\n")
                logger.info(f"验证成功的结果已保存到: {verified_dir}")
        else:
            # 即使未成功，也输出保存位置
            print(f"\n{'='*60}")
            print(f"[INFO] 结果已保存到:")
            print(f"{'='*60}")
            print(f"  - {result_dir}")
            print(f"    - formal_sketch.txt")
            if informal_proof:
                print(f"    - informal_proof.txt")
            if theory_file and theory_file.exists():
                print(f"    - {theorem_name}.thy")
            print(f"    - result.json")
            print(f"{'='*60}\n")
            logger.info(f"结果已保存到: {result_dir}")
    
    def _build_delivery_bundle(
        self,
        theorem_name: str,
        result: Dict,
        theorem_data: Dict,
    ) -> None:
        """证明成功后生成交付包：results/<domain>/<theorem>/（论文 3.2.1 / 4.1.2）。"""
        if not getattr(self.config, "delivery_enabled", True):
            return
        try:
            domain = resolve_domain(theorem_data)
        except Exception as exc:
            logger.warning("交付包跳过（无法解析 domain）: %s", exc)
            return
        from .eval.delivery_bundle import build_delivery_bundle

        try:
            bundle = build_delivery_bundle(
                output_dir=self.config.output_dir,
                domain=domain,
                theorem_name=theorem_name,
                result=result,
                theorem_data=theorem_data,
                delivery_dir=getattr(self.config, "delivery_dir", None),
                data_dir=getattr(self.config, "data_dir", None),
            )
        except Exception as exc:
            logger.warning("交付包生成失败: %s", exc, exc_info=True)
            return
        result["delivery_dir"] = str(bundle)
        print(f"\n[delivery] 交付包已生成: {bundle}", flush=True)

    def _generate_summary(self, results: List[Dict]):
        """生成摘要报告"""
        total = len(results)
        success = sum(1 for r in results if r.get("status") == "success")
        summary = {
            "total": total,
            "success": success,
            "success_rate": success / total if total > 0 else 0.0
        }
        
        summary_file = Path(self.config.output_dir) / "summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        
        logger.info(f"摘要: {success}/{total} 成功")
    
    def close(self):
        """关闭资源并清理 Isabelle server/PolyML 子进程。"""
        if self.lemma_cache:
            self.lemma_cache.save()
        n = shutdown_all_isabelle_servers(reason="prover.close")
        if n:
            print(
                f"[isabelle_server] 已清理 {n} 个遗留 server/session",
                flush=True,
            )


def main():
    """主函数"""
    # 设置Windows终端编码
    import sys
    log_file_handle = None
    original_stdout = sys.stdout
    original_stderr = sys.stderr
    if sys.platform == 'win32':
        import io
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
        sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')
    original_stdout = sys.stdout
    original_stderr = sys.stderr
    
    parser = argparse.ArgumentParser(description="BLProver: 基于引理的 Isabelle 定理证明系统")
    
    parser.add_argument(
        "--data-dir", "-d",
        type=str,
        default="./data",
        help="定理数据目录"
    )
    
    parser.add_argument(
        "--output-dir", "-o",
        type=str,
        default="./output",
        help="输出目录"
    )
    
    parser.add_argument(
        "--single", "-s",
        type=str,
        help="单个定理文件"
    )
    
    parser.add_argument(
        "--count", "-n",
        type=int,
        help="处理数量限制"
    )
    
    parser.add_argument(
        "--model",
        type=str,
        default="deepseek-v4-pro",
        help="LLM模型名称"
    )
    parser.add_argument(
        "--skip-sledgehammer",
        action="store_true",
        help="跳过生成 .thy 后的 sledgehammer 回填与 Isabelle 验证（默认会执行）",
    )
    parser.add_argument(
        "--rebuild-delivery",
        action="store_true",
        help="不重新证明，按交付包快照重算 metrics 并同步库级聚合视图与根 README",
    )
    parser.add_argument(
        "--experiment-metrics",
        action="store_true",
        help="只汇总实验指标（论文 4.1.2），不证明；报告写入 results/experiment_metrics/",
    )
    parser.add_argument(
        "--no-delivery",
        action="store_true",
        help="证明成功后不生成交付包（默认生成到 results/<domain>/<theorem>/）",
    )
    parser.add_argument(
        "--delivery-dir",
        type=str,
        default=None,
        help="交付包根目录（默认 <output_dir>/results）",
    )
    parser.add_argument(
        "--verify-thy-file",
        type=str,
        help="仅执行指定 .thy 的 sledgehammer 回填与验证",
    )
    parser.add_argument(
        "--isabelle-path",
        type=str,
        default="D:/software/Isabelle2025/Isabelle2025/contrib/cygwin/bin/bash.exe",
        help="Isabelle bash 路径（用于 .thy 验证）",
    )
    parser.add_argument(
        "--isabelle-home",
        type=str,
        default="D:/software/Isabelle2025/Isabelle2025",
        help="Isabelle HOME（用于 .thy 验证）",
    )
    parser.add_argument(
        "--isabelle-timeout",
        type=int,
        default=60,
        help="Isabelle sledgehammer 阶段 use_theories 超时（秒，上限 60）",
    )
    parser.add_argument(
        "--isabelle-verify-timeout",
        type=int,
        default=60,
        help="纯验证 / repair 后 verify 超时（秒，上限 60）",
    )
    parser.add_argument(
        "--isabelle-verify-wall-timeout",
        type=int,
        default=300,
        help="verify wall-clock 硬超时（秒，上限 600）；大理论加载慢时可增大",
    )
    parser.add_argument(
        "--sledgehammer-rounds",
        type=int,
        default=3,
        help="sledgehammer 回填最大轮次（论文 4.1.4：内层回填 3 次）",
    )
    parser.add_argument(
        "--repair-rounds",
        type=int,
        default=3,
        help="验证失败后，按报错行定向替换为 sledgehammer 的最大轮次（论文 4.1.4：内层修复 3 次）",
    )
    parser.add_argument(
        "--no-repair-failed-steps",
        action="store_true",
        help="关闭验证失败后的定向 sledgehammer 修复",
    )
    parser.add_argument(
        "--sketch-repair-attempts",
        type=int,
        default=3,
        help="Sledgehammer/Isabelle 验证失败后，根据错误信息让 LLM 重生成草图的最大次数（默认 3）",
    )
    parser.add_argument(
        "--no-sketch-repair",
        action="store_true",
        help="关闭验证失败后的 LLM 草图修复循环",
    )
    parser.add_argument(
        "--no-repair-lemma",
        action="store_true",
        help="关闭验证失败后的修复引理构造 + 引理修正机制（论文 2.3.3）",
    )
    parser.add_argument(
        "--sketch-repair-prompt",
        type=str,
        default=None,
        help="草图修复提示词路径（默认 prompt/sketch_repair_after_verify_prompt.txt）",
    )
    parser.add_argument(
        "--no-prove-used-lemmas",
        action="store_true",
        help="主定理验证通过后，不自动迭代证明 unproven 中的 sorry 引理",
    )
    parser.add_argument(
        "--quality-eval-only",
        action="store_true",
        help="跳过证明，直接对已有产物执行引理质量评估与筛选（论文 3.1/3.2）",
    )
    parser.add_argument(
        "--used-lemma-initial-attempts",
        type=int,
        default=3,
        help="每条引理首次生成（lemma_proof_prompt）最大轮次（默认 3）",
    )
    parser.add_argument(
        "--used-lemma-repair-attempts",
        type=int,
        default=3,
        help="每条引理单次首次失败后的修复（lemma_proof_repair_prompt）最大轮次（默认 3）",
    )
    parser.add_argument(
        "--used-lemma-llm-attempts",
        type=int,
        default=None,
        help="已弃用：等同 --used-lemma-initial-attempts",
    )
    parser.add_argument(
        "--lemma-proof-prompt",
        type=str,
        default=None,
        help="引理首次证明 prompt（默认 lemma_proving/lemma_proof_prompt.txt）",
    )
    parser.add_argument(
        "--lemma-proof-repair-prompt",
        type=str,
        default=None,
        help="引理证明失败后修复 prompt（默认 lemma_proving/lemma_proof_repair_prompt.txt）",
    )
    parser.add_argument(
        "--isabelle-server",
        action="store_true",
        default=True,
        help="使用 isabelle_client server 模式进行 .thy 验证（默认开启）",
    )
    parser.add_argument(
        "--no-isabelle-server",
        action="store_true",
        help="关闭 server 模式，回退 CLI 模式",
    )
    
    parser.add_argument(
        "--enable-chroma-lemmas",
        action="store_true",
        help="启用 ChromaDB 已证/未证引理库（默认关闭；不删除 chroma_lemma_db 内已有数据）",
    )
    
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="控制台输出全部内部细节（默认仅输出阶段与关键事件，细节仅写入日志文件）",
    )
    parser.add_argument(
        "--log-level",
        type=str,
        default="INFO",
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="日志级别"
    )
    
    args = parser.parse_args()

    # 每次运行自动落盘完整日志（stdout/stderr + logging）
    output_dir = Path(args.output_dir)
    log_dir = output_dir / "logs"
    log_stem = resolve_main_run_log_stem(
        single=args.single,
        verify_thy_file=args.verify_thy_file,
        data_dir=args.data_dir,
    )
    log_path = run_log_path(log_dir, log_stem)
    log_file_handle = open(log_path, "w", encoding="utf-8")
    console_filter = ConsoleLineFilter(verbose=bool(args.verbose))
    set_verbose(bool(args.verbose))
    sys.stdout = _TeeStream(
        sys.stdout, log_file_handle, console_filter=console_filter
    )
    sys.stderr = _TeeStream(
        sys.stderr, log_file_handle, console_filter=console_filter
    )
    attach_stream(sys.stdout)
    print(f"[log] 本次运行日志文件: {log_path}")
    
    # 配置日志
    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format='%(name)s - %(levelname)s - %(message)s'
    )

    runner_config = IsabelleRunnerConfig(
        isabelle_path=args.isabelle_path,
        isabelle_home=args.isabelle_home,
        timeout=args.isabelle_timeout,
        verify_timeout=args.isabelle_verify_timeout,
        verify_wall_timeout_sec=args.isabelle_verify_wall_timeout,
        max_sledgehammer_rounds=args.sledgehammer_rounds,
        max_failure_repair_rounds=args.repair_rounds,
        repair_failed_steps=not args.no_repair_failed_steps,
        use_server=(args.isabelle_server and not args.no_isabelle_server),
    )

    if args.rebuild_delivery:
        # 论文 4.1.2：用已有交付包的快照重算指标（不证明任何定理）
        from .eval.delivery_bundle import delivery_root, rebuild_delivery_metrics

        rebuilt = rebuild_delivery_metrics(
            output_dir,
            delivery_root(output_dir, args.delivery_dir),
            data_dir=args.data_dir,
        )
        print(
            f"\n[rebuild-delivery] 已重建 {rebuilt} 个交付包的 metrics，并同步库级聚合视图与根 README"
        )
        if log_file_handle:
            log_file_handle.flush()
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            log_file_handle.close()
        return

    if args.experiment_metrics:
        # 论文 4.1.2：从运行产物汇总实验指标（只读产物、写报告）
        from .eval.experiment_metrics import collect_metrics, write_metrics

        metrics = collect_metrics(output_dir, data_dir=args.data_dir)
        metrics_dir = write_metrics(output_dir, metrics)
        tp = metrics.get("theorem_proving") or {}
        gen = metrics.get("lemma_generation_efficiency") or {}
        scr = metrics.get("lemma_screening_effectiveness") or {}
        reuse = metrics.get("lemma_library_reuse") or {}
        print(
            "\n[experiment-metrics] 引理总数=%s（来源 %s）；淘汰率=%s；复用率(论文 4.1.2 主口径:仅定理引用)=%s；定理成功率=%s" % (
                gen.get("total"),
                gen.get("by_source"),
                scr.get("elimination_rate"),
                reuse.get("reuse_rate"),
                tp.get("success_rate_attempted"),
            )
        )
        print(f"[experiment-metrics] 报告: {metrics_dir / 'metrics.json'} , {metrics_dir / 'metrics.md'}")
        if log_file_handle:
            log_file_handle.flush()
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            log_file_handle.close()
        return

    if args.verify_thy_file:
        processed = verify_thy_with_repair(args.verify_thy_file, runner_config)
        print_thy_verify_result(processed)
        if log_file_handle:
            log_file_handle.flush()
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            log_file_handle.close()
        return
    
    config = BLProverConfig(
        output_dir=args.output_dir,
        data_dir=args.data_dir,
        llm=LLMConfig(model_name=args.model),
        lemma_cache=LemmaCacheConfig(chroma_enabled=args.enable_chroma_lemmas),
        max_sketch_repair_attempts=max(0, args.sketch_repair_attempts),
        sketch_repair_enabled=not args.no_sketch_repair,
        repair_lemma_enabled=not args.no_repair_lemma,
        prove_used_lemmas_after_theorem=not args.no_prove_used_lemmas,
        used_lemma_initial_max_attempts=max(
            1,
            args.used_lemma_initial_attempts
            if args.used_lemma_llm_attempts is None
            else args.used_lemma_llm_attempts,
        ),
        used_lemma_repair_max_attempts=max(1, args.used_lemma_repair_attempts),
        delivery_enabled=not args.no_delivery,
        delivery_dir=args.delivery_dir,
    )
    if args.sketch_repair_prompt:
        config.sketch_repair_prompt_path = args.sketch_repair_prompt
    if args.lemma_proof_prompt:
        config.lemma_proof_prompt_path = args.lemma_proof_prompt
    if args.lemma_proof_repair_prompt:
        config.lemma_proof_repair_prompt_path = args.lemma_proof_repair_prompt

    run_sledgehammer = not args.skip_sledgehammer
    need_isabelle_runner = run_sledgehammer or (
        config.lemma_quality_eval.enabled
        and config.lemma_quality_eval.syntax_enabled
    )
    prover = BLProver(
        config,
        isabelle_runner=runner_config if need_isabelle_runner else None,
        run_sledgehammer_after_thy=run_sledgehammer,
    )
    
    try:
        if args.quality_eval_only:
            # 只跑质量评估 + 质量筛选（论文 3.1/3.2），不重新证明
            theorem_data = prover._load_theorem_data(args.single)
            theorem_name = theorem_data.get("theorem name", "theorem")
            domain = resolve_domain(theorem_data, args.single)
            theory_dir = theorem_theory_dir(
                config.output_dir, domain, theorem_name
            )
            # 复用上次结果中的 status / final_theory_file，使引用保护与正常流程一致
            qe_result: Dict = {}
            prev_result_file = (
                Path(config.output_dir) / "results" / theorem_name / "result.json"
            )
            if prev_result_file.is_file():
                try:
                    qe_result = json.loads(
                        prev_result_file.read_text(encoding="utf-8")
                    )
                except Exception:
                    qe_result = {}
            prover._run_proven_lemma_library_quality_eval(
                theorem_name,
                theory_dir,
                domain,
                qe_result,
                advance_batch=False,
            )
            screening = qe_result.get("quality_screening") or {}
            if _theorem_verified(qe_result):
                print(
                    "\n质量筛选: total=%s eliminated=%s rate=%s removed=%s"
                    % (
                        screening.get("total"),
                        screening.get("eliminated_count"),
                        screening.get("elimination_rate"),
                        screening.get("removed"),
                    )
                )
            else:
                print(
                    "\n质量筛选: 跳过（定理未证明成功；"
                    "论文 4.1.2 主口径只统计证明成功定理的引用）"
                )
            print("\n结果: quality_eval_only")
        elif args.single:
            # 证明单个定理
            result = prover.prove_theorem(args.single)
            print(f"\n结果: {result['status']}")
        else:
            # 批量证明
            results = prover.prove_batch(args.data_dir, args.count)
            print(f"\n完成: {len(results)} 个定理")
    except KeyboardInterrupt:
        n = shutdown_all_isabelle_servers(reason="KeyboardInterrupt")
        if n:
            print(
                f"\n[isabelle_server] Ctrl+C 已清理 {n} 个 server/session",
                flush=True,
            )
        raise
    finally:
        prover.close()
        if log_file_handle:
            log_file_handle.flush()
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            log_file_handle.close()


if __name__ == "__main__":
    main()
