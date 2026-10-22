"""
Sledgehammer/Isabelle 验证失败后的 formal sketch 迭代修复。

提示词：BLProver/prompt/sketch_repair_after_verify_prompt.txt
User 区 3 个占位符 {{}}（顺序）：
  1. 草图修复上下文：*_sketch.thy + 已 import 的 defs/unproven .thy 正文
     + proven_lemmas.thy 中被主定理 proof 直接引用的引理子集（无命中则省略）
  2. Isabelle 错误输出
  3. 构造草图阶段的 informal proof

模型输出：JSON（proof / extra_lemmas / explanation / informal_proof）
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

from ..config import BLProverConfig
from ..lemma.unproven_lemma_store import UnprovenLemmaStore
from ..lemma.proven_lemma_store import PROVEN_THEORY_NAME
from ..lemma_proving.usage import (
    extract_main_theorem_proof_region,
    lemma_blocks_in_thy,
)
from ..utils.isabelle_sledgehammer import (
    format_isabelle_error_for_prompt,
    process_sledgehammer_and_verify,
)
from ..utils.lemma_dedup import (
    collect_lemma_refs_from_proof,
    extract_fact_name,
    extract_sketch_main_theorem,
    split_non_main_facts_from_sketch,
    truncate_theory_to_first_closure,
)

logger = logging.getLogger(__name__)

SKETCH_REPAIR_PLACEHOLDER = "{{}}"
SKETCH_REPAIR_USER_PLACEHOLDERS = 3
SKETCH_REPAIR_PROMPT_FILENAME = "sketch_repair_after_verify_prompt.txt"

_JSON_FENCE_RE = re.compile(
    r"```(?:json)?\s*(\{.*?\})\s*```",
    re.DOTALL | re.IGNORECASE,
)

_BEGIN_LINE_RE = re.compile(r"^\s*begin\s*$", re.IGNORECASE)
_FACT_DECL_LINE_RE = re.compile(
    r"^\s*(lemma|theorem|corollary|proposition)\s+",
    re.IGNORECASE,
)


def default_sketch_repair_prompt_path(pkg_root: Path) -> Path:
    return pkg_root / "prompt" / SKETCH_REPAIR_PROMPT_FILENAME


def _extract_theory_header(text: str) -> str:
    """返回 `theory ... begin` 头部（含 begin 行）；无 begin 时回退到首个 fact 行之前。"""
    lines = (text or "").splitlines()
    for i, line in enumerate(lines):
        if _BEGIN_LINE_RE.match(line):
            return "\n".join(lines[: i + 1])
    for i, line in enumerate(lines):
        if _FACT_DECL_LINE_RE.match(line):
            return "\n".join(lines[:i])
    return (text or "").strip()


def _filter_proven_lemmas_to_referenced(
    sketch_thy_text: str,
    proven_thy_text: str,
    theorem_name: Optional[str],
) -> str:
    """
    从 proven_lemmas.thy 文本中只挑出主定理 proof 直接引用的引理块，
    重新包裹为自洽的 theory 文本（保留原 theory/imports/begin 头与 end）。

    无命中（库为空、proof 无引用、引用名都不在库中）时返回空串，
    调用方据此省略 proven 段，避免发送整库消耗 token。
    """
    if not (proven_thy_text or "").strip():
        return ""

    refs: Set[str] = set()
    if theorem_name:
        proof_region = extract_main_theorem_proof_region(
            sketch_thy_text or "", theorem_name
        )
        if proof_region.strip():
            refs = collect_lemma_refs_from_proof(proof_region)
    # 主定理 proof 区域解析失败时回退：扫描整个 sketch 文本中的引用
    if not refs:
        refs = collect_lemma_refs_from_proof(sketch_thy_text or "")
    if not refs:
        return ""

    blocks = lemma_blocks_in_thy(proven_thy_text)
    if not blocks:
        return ""

    # 保留 proven_lemmas.thy 中的声明顺序
    picked_names = [n for n in blocks.keys() if n in refs]
    if not picked_names:
        return ""

    header = _extract_theory_header(proven_thy_text)
    body = "\n\n".join(blocks[n] for n in picked_names)
    return f"{header}\n\n{body}\n\nend\n"


def build_sketch_repair_thy_prompt_context(
    sketch_thy_text: str,
    *,
    unproven_thy_path: Optional[Path] = None,
    proven_thy_path: Optional[Path] = None,
    defs_thy_path: Optional[Path] = None,
    theorem_name: Optional[str] = None,
) -> str:
    """
    组装发给 LLM 的「.thy 上下文」：工作 sketch 文件 + 其 imports 的 defs/unproven/proven 理论正文。

    proven_lemmas.thy 只注入主定理 proof 直接引用的引理块（避免整库上百条全部塞入提示词，
    导致 token 浪费与注意力分散）；无引用命中时整段省略。
    """
    sections: List[str] = []
    sketch = truncate_theory_to_first_closure((sketch_thy_text or "").strip())
    if sketch:
        sections.append(
            "=== Working file (*_sketch.thy; fix ONLY the main theorem proof here) ===\n"
            + sketch
        )

    if defs_thy_path and defs_thy_path.is_file():
        defs_text = truncate_theory_to_first_closure(
            defs_thy_path.read_text(encoding="utf-8")
        )
        if defs_text:
            sections.append(
                f"=== Imported: {defs_thy_path.name} "
                "(global function/type definitions; available via import) ===\n"
                + defs_text
            )

    if unproven_thy_path and unproven_thy_path.is_file():
        unproven = truncate_theory_to_first_closure(
            unproven_thy_path.read_text(encoding="utf-8")
        )
        if unproven:
            sections.append(
                f"=== Imported: {unproven_thy_path.name} "
                "(lemmas to prove, some may use sorry; available via import) ===\n"
                + unproven
            )

    if proven_thy_path and proven_thy_path.is_file():
        proven_filtered = _filter_proven_lemmas_to_referenced(
            sketch_thy_text or "",
            proven_thy_path.read_text(encoding="utf-8"),
            theorem_name,
        )
        if proven_filtered:
            sections.append(
                f"=== Imported: {proven_thy_path.name} "
                "(already-proven lemmas from global library; only those referenced by "
                "the failing proof are shown — others exist via import but are omitted "
                "to save context) ===\n"
                + proven_filtered
            )

    return "\n\n".join(sections) if sections else ""


def fill_sketch_repair_user_template(
    user_template: str,
    thy_content: str,
    isabelle_error: str,
    informal_proof: str,
    prompt_path: str,
) -> str:
    replacements = [
        (thy_content or "").strip(),
        (isabelle_error or "").strip(),
        (informal_proof or "").strip(),
    ]
    count = user_template.count(SKETCH_REPAIR_PLACEHOLDER)
    if count != SKETCH_REPAIR_USER_PLACEHOLDERS:
        raise ValueError(
            f"草图修复提示词占位符 {SKETCH_REPAIR_PLACEHOLDER!r} 数量应为 "
            f"{SKETCH_REPAIR_USER_PLACEHOLDERS}，实际为 {count}: {prompt_path}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(SKETCH_REPAIR_PLACEHOLDER, block, 1)
    return out


_VALID_JSON_ESCAPE_LEAD = frozenset('"\\/bfnrtu')


def _sanitize_json_invalid_backslashes(text: str) -> str:
    """
    Isabelle 符号常写成 \\<not>、\\<Longrightarrow> 等；在 JSON 字符串里 \\< 不是合法转义。
    将字符串字面量内的非法反斜杠加倍，使 json.loads 可解析。
    """
    out: List[str] = []
    i = 0
    n = len(text)
    in_string = False
    while i < n:
        ch = text[i]
        if not in_string:
            out.append(ch)
            if ch == '"':
                in_string = True
            i += 1
            continue
        if ch == '"':
            in_string = False
            out.append(ch)
            i += 1
            continue
        if ch == "\\":
            if i + 1 >= n:
                out.append("\\\\")
                i += 1
                continue
            nxt = text[i + 1]
            if nxt == "u":
                hex_part = text[i + 2 : i + 6]
                if len(hex_part) == 4 and all(
                    c in "0123456789abcdefABCDEF" for c in hex_part
                ):
                    out.append(text[i : i + 6])
                    i += 6
                    continue
                out.append("\\\\")
                i += 1
                continue
            if nxt in _VALID_JSON_ESCAPE_LEAD:
                out.append(ch)
                out.append(nxt)
                i += 2
                continue
            out.append("\\\\")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _loads_sketch_repair_json(text: str) -> Dict[str, Any]:
    last_exc: Optional[json.JSONDecodeError] = None
    for candidate in (text, _sanitize_json_invalid_backslashes(text)):
        try:
            data = json.loads(candidate)
            if isinstance(data, dict):
                return data
            raise ValueError("草图修复 JSON 根节点必须是 object")
        except json.JSONDecodeError as exc:
            last_exc = exc
    assert last_exc is not None
    raise last_exc


def parse_sketch_repair_json(raw: str) -> Dict[str, Any]:
    """从 LLM 回复中解析修复 JSON。"""
    text = (raw or "").strip()
    if not text:
        raise ValueError("草图修复 LLM 返回为空")

    fence = _JSON_FENCE_RE.search(text)
    if fence:
        text = fence.group(1).strip()
    else:
        start = text.find("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            text = text[start : end + 1]

    data = _loads_sketch_repair_json(text)
    if not isinstance(data, dict):
        raise ValueError("草图修复 JSON 根节点必须是 object")
    if not (data.get("proof") or "").strip():
        raise ValueError("草图修复 JSON 缺少非空 proof 字段")
    return data


def upsert_combined_lemma_statements(
    statements: List[str],
    new_blocks: Dict[str, str],
) -> List[str]:
    """按引理名更新 combined_lemma_statements，供后续 lemma_usage 使用。"""
    by_name: Dict[str, int] = {}
    out = list(statements)
    for i, stmt in enumerate(out):
        name = extract_fact_name(stmt)
        if name:
            by_name[name] = i
    for name, block in new_blocks.items():
        text = (block or "").strip()
        if not text:
            continue
        if name in by_name:
            out[by_name[name]] = text
        else:
            out.append(text)
            by_name[name] = len(out) - 1
    return out


def sanitize_sketch_repair_payload(
    data: Dict[str, Any],
    theorem_name: str,
) -> Dict[str, Any]:
    """
    清洗 LLM 修复 JSON：proof 只保留主定理；误放的引理/整份 .thy 回显拆入 extra_lemmas。
    """
    proof_raw = (data.get("proof") or "").strip()
    extra_raw = (data.get("extra_lemmas") or "").strip()

    main, from_proof = split_non_main_facts_from_sketch(proof_raw, theorem_name)
    if not (main or "").strip():
        main = extract_sketch_main_theorem(proof_raw, theorem_name)
    if not (main or "").strip():
        raise ValueError("proof 清洗后为空（可能缺少主定理声明）")

    merged_extra = [p for p in (extra_raw, from_proof.strip()) if p]
    return {
        **data,
        "proof": main.strip(),
        "extra_lemmas": "\n\n".join(merged_extra).strip(),
    }


def sketch_text_from_repair_json(data: Dict[str, Any]) -> str:
    """将 JSON 的 proof 作为注入 *_sketch.thy 的正文（extra_lemmas 由 unproven 路径单独合并）。"""
    proof = (data.get("proof") or "").strip()
    if not proof:
        raise ValueError("proof 为空")
    return proof


@dataclass
class SketchRepairLoopContext:
    """单次定理修复循环所需的上下文。"""

    theorem_name: str
    theorem_data: Dict[str, Any]
    informal_proof: str
    combined_lemma_statements: List[str]
    theory_dir: Path
    result_dir: Path
    sketch: str
    theory_file: Path
    run_artifact: Any
    isabelle_runner: Any
    print_verify_result: Callable[[dict], None]
    create_theory_file: Callable[..., Optional[Path]]
    server_pool: Any = None


@dataclass
class SketchRepairLoopResult:
    sketch: str
    theory_file: Optional[Path]
    processed: dict
    repair_attempts: int = 0
    history: List[Dict[str, Any]] = field(default_factory=list)


class SketchRepairRunner:
    """加载 sketch_repair_after_verify_prompt.txt，验证失败后按 JSON 修复证明。"""

    def __init__(
        self,
        config: BLProverConfig,
        *,
        load_prompt_template: Callable[[str], Tuple[str, str]],
        call_stage_llm: Callable[[str, str, str], str],
    ):
        self.config = config
        self._load_prompt_template = load_prompt_template
        self._call_stage_llm = call_stage_llm
        prompt_path = config.sketch_repair_prompt_path
        if not prompt_path or not Path(prompt_path).is_file():
            raise FileNotFoundError(
                f"草图修复提示词不存在: {prompt_path}\n"
                f"请编辑 {SKETCH_REPAIR_PROMPT_FILENAME}（与 sketch_repair.py 配套）"
            )
        self._prompt_path = prompt_path

    @property
    def prompt_path(self) -> str:
        return self._prompt_path

    def regenerate_sketch(
        self,
        thy_content: str,
        isabelle_error: str,
        informal_proof: str,
        repair_attempt: int,
        max_repair_attempts: int,
        *,
        theorem_name: str,
    ) -> Tuple[str, str, Dict[str, Any]]:
        sys_prompt, user_tpl = self._load_prompt_template(self._prompt_path)
        header = f"(Repair attempt {repair_attempt} of {max_repair_attempts})\n\n"
        user_prompt = fill_sketch_repair_user_template(
            user_tpl,
            header + thy_content,
            header + isabelle_error,
            informal_proof,
            self._prompt_path,
        )
        stage_name = f"sketch_repair_{repair_attempt}"
        raw = self._call_stage_llm(stage_name, sys_prompt, user_prompt)
        try:
            parsed = sanitize_sketch_repair_payload(
                parse_sketch_repair_json(raw),
                theorem_name,
            )
            sketch = sketch_text_from_repair_json(parsed)
        except (json.JSONDecodeError, ValueError) as exc:
            logger.error("草图修复 JSON 解析失败: %s", exc)
            raise ValueError(f"{stage_name} 输出不是合法修复 JSON: {exc}") from exc
        return sketch, raw, parsed

    def run_repair_loop(
        self,
        ctx: SketchRepairLoopContext,
        initial_processed: dict,
    ) -> SketchRepairLoopResult:
        max_repairs = (
            self.config.max_sketch_repair_attempts
            if self.config.sketch_repair_enabled
            else 0
        )
        processed = initial_processed
        sketch = ctx.sketch
        theory_file = ctx.theory_file
        history: List[Dict[str, Any]] = []
        repair_attempt = 0

        ctx.result_dir.mkdir(parents=True, exist_ok=True)

        while not processed.get("success") and repair_attempt < max_repairs:
            repair_attempt += 1
            unproven_thy_name = f"{ctx.theorem_name}_unproven_lemmas"
            # stuck_repair 可能已将 .thy 中的证明步改为 sledgehammer；修复前还原为当前 sketch
            theory_file = ctx.create_theory_file(
                {**ctx.theorem_data, "theorem name": ctx.theorem_name},
                sketch,
                ctx.theory_dir,
                unproven_thy_name,
            )
            if not theory_file or not theory_file.exists():
                logger.error("草图修复需要 .thy 文件，但路径不存在")
                break

            raw_thy = theory_file.read_text(encoding="utf-8")
            thy_content = truncate_theory_to_first_closure(raw_thy)
            if thy_content != raw_thy:
                theory_file.write_text(thy_content, encoding="utf-8")
            err_formatted = format_isabelle_error_for_prompt(
                processed.get("verify_output") or ""
            )
            error_file = (
                ctx.result_dir / f"isabelle_error_repair_{repair_attempt}.txt"
            )
            error_file.write_text(err_formatted, encoding="utf-8")

            unproven_path = ctx.theory_dir / f"{unproven_thy_name}.thy"
            domain_dir = ctx.theory_dir.parent
            domain = ctx.theorem_data.get("domain") or domain_dir.name
            proven_path = domain_dir / f"{PROVEN_THEORY_NAME}.thy"
            defs_path = domain_dir / "defs.thy"
            thy_for_prompt = build_sketch_repair_thy_prompt_context(
                thy_content,
                unproven_thy_path=unproven_path,
                proven_thy_path=proven_path,
                defs_thy_path=defs_path,
                theorem_name=ctx.theorem_name,
            )
            (ctx.result_dir / f"thy_input_repair_{repair_attempt}.thy").write_text(
                thy_for_prompt, encoding="utf-8"
            )

            logger.info(
                "Isabelle 验证失败，开始草图修复 %d/%d（prompt=%s）",
                repair_attempt,
                max_repairs,
                self._prompt_path,
            )
            print(
                f"\n[sketch-repair {repair_attempt}/{max_repairs}] "
                f"输入: sketch + "
                f"{'defs ' if defs_path.is_file() else ''}"
                f"{'unproven ' if unproven_path.is_file() else ''}"
                f"{'proven ' if proven_path.is_file() else ''}"
                f".thy + Isabelle 错误 + informal proof",
                flush=True,
            )

            try:
                sketch, repair_raw, parsed_json = self.regenerate_sketch(
                    thy_for_prompt,
                    err_formatted,
                    ctx.informal_proof,
                    repair_attempt,
                    max_repairs,
                    theorem_name=ctx.theorem_name,
                )
            except ValueError as exc:
                history.append(
                    {
                        "attempt": repair_attempt,
                        "success": False,
                        "error": str(exc),
                        "isabelle_error_file": str(error_file),
                    }
                )
                break

            ctx.run_artifact.append_sketch(1 + repair_attempt, sketch)
            (ctx.result_dir / f"formal_sketch_repair_{repair_attempt}.txt").write_text(
                sketch, encoding="utf-8"
            )
            (ctx.result_dir / f"formal_sketch_repair_{repair_attempt}_raw.txt").write_text(
                repair_raw, encoding="utf-8"
            )
            (ctx.result_dir / f"sketch_repair_{repair_attempt}.json").write_text(
                json.dumps(parsed_json, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )

            extra = (parsed_json.get("extra_lemmas") or "").strip()
            merged_names: List[str] = []
            if extra:
                extra_blocks = UnprovenLemmaStore.parse_extra_lemma_blocks(extra)
                if ctx.theorem_name in extra_blocks:
                    logger.warning(
                        "extra_lemmas 含主定理 %s，跳过并入 unproven（避免与 sketch 重复）",
                        ctx.theorem_name,
                    )
                    extra_blocks.pop(ctx.theorem_name, None)
                if extra_blocks:
                    extra = "\n\n".join(extra_blocks.values())
                else:
                    extra = ""
            if extra:
                packages = (ctx.theorem_data.get("packages") or "Main").strip()
                merged_names = UnprovenLemmaStore.merge_extra_lemmas_into_unproven_thy(
                    unproven_path,
                    extra,
                    unproven_thy_name,
                    packages=packages,
                    theorem_data=ctx.theorem_data,
                    domain=domain,
                )
                if merged_names:
                    extra_blocks = UnprovenLemmaStore.parse_extra_lemma_blocks(extra)
                    ctx.combined_lemma_statements = upsert_combined_lemma_statements(
                        ctx.combined_lemma_statements,
                        {
                            n: extra_blocks[n]
                            for n in merged_names
                            if n in extra_blocks
                        },
                    )
                    print(
                        f"\n[sketch-repair] extra_lemmas 已并入 {unproven_path.name}: "
                        f"{', '.join(merged_names)}",
                        flush=True,
                    )

            theory_file = ctx.create_theory_file(
                {**ctx.theorem_data, "theorem name": ctx.theorem_name},
                sketch,
                ctx.theory_dir,
                unproven_thy_name,
            )
            if not theory_file or not theory_file.exists():
                logger.error("草图修复后未能生成 .thy 文件")
                history.append(
                    {
                        "attempt": repair_attempt,
                        "success": False,
                        "error": "theory_file_not_created",
                        "isabelle_error_file": str(error_file),
                    }
                )
                break

            processed = process_sledgehammer_and_verify(
                str(theory_file),
                ctx.isabelle_runner,
                server_pool=ctx.server_pool,
            )
            ctx.print_verify_result(processed)
            history.append(
                {
                    "attempt": repair_attempt,
                    "success": bool(processed.get("success")),
                    "isabelle_error_file": str(error_file),
                    "thy_input_file": str(
                        ctx.result_dir / f"thy_input_repair_{repair_attempt}.thy"
                    ),
                    "sketch_repair_prompt": self._prompt_path,
                    "repair_explanation": (parsed_json.get("explanation") or ""),
                    "merged_extra_lemmas": merged_names,
                    "sledgehammer_replaced": processed.get(
                        "replaced_sledgehammer_count", 0
                    ),
                    "failure_repair_count": processed.get(
                        "failure_repair_count", 0
                    ),
                }
            )

        if (
            not processed.get("success")
            and repair_attempt >= max_repairs
            and max_repairs > 0
        ):
            logger.info(
                "已完成 %d 次草图修复仍验证失败（prompt=%s）",
                max_repairs,
                self._prompt_path,
            )

        return SketchRepairLoopResult(
            sketch=sketch,
            theory_file=theory_file,
            processed=processed,
            repair_attempts=repair_attempt,
            history=history,
        )
