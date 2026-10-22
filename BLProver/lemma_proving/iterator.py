"""
单条引理 LLM 迭代证明：LLM → Isabelle → sledgehammer → 错误反馈。

提示词：同目录 lemma_proof_prompt.txt
"""

from __future__ import annotations

import logging
import re
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from ..config import BLProverConfig
from ..sketch.prompt_paths import HIDDEN_FULL_PROOF_PROMPT
from ..llm.base import LLMInterface
from ..utils.isabelle_sledgehammer import (
    IsabelleRunnerConfig,
    IsabelleServerSessionPool,
    format_isabelle_error_for_prompt,
    iter_isabelle_server_error_messages,
    prepare_session_for_lemma_proof_verify,
    prepare_session_for_lemma_llm_repair,
    prepare_session_for_repair_final_verify,
    process_sledgehammer_and_verify,
    _is_stuck_verify_output,
    _mark_thy_disk_changed,
    _repair_failed_steps_with_sledgehammer,
    _repair_stuck_verify_with_sledgehammer,
    _run_use_thy,
    _verification_passed,
)
from ..utils.lemma_dedup import collect_lemma_refs_from_proof, expand_lemma_ref_closure
from .usage import lemma_blocks_in_thy, lemma_still_sorry

logger = logging.getLogger(__name__)

LEMMA_PROOF_PLACEHOLDER = "{{}}"
LEMMA_PROOF_PLACEHOLDERS = 2
LEMMA_PROOF_PROMPT_FILENAME = "lemma_proof_prompt.txt"
LEMMA_PROOF_REPAIR_PROMPT_FILENAME = "lemma_proof_repair_prompt.txt"
LEMMA_PROOF_REPAIR_PLACEHOLDERS = 4
_LEMMA_PROOF_TASK_SPLIT = re.compile(
    r"####\s*below\s+are\s+your\s+task",
    re.IGNORECASE,
)
_ISABELLE_FENCE_RE = re.compile(
    r"```(?:isabelle)?\s*(.*?)```",
    re.DOTALL | re.IGNORECASE,
)
_LEMMA_PROOF_SECTION_RE = re.compile(
    r"###\s*(?:Lemma proof|引理证明)\s*\n(.*?)(?=###\s*(?:Proof strategy|证明思路)|\Z)",
    re.DOTALL | re.IGNORECASE,
)
_PROOF_STRATEGY_SECTION_RE = re.compile(
    r"###\s*(?:Proof strategy|证明思路)\s*\n(.*)",
    re.DOTALL | re.IGNORECASE,
)
_REPAIR_STRATEGY_SECTION_RE = re.compile(
    r"###\s*(?:Repair strategy|修复思路)\s*\n(.*)",
    re.DOTALL | re.IGNORECASE,
)
_SHOWS_ASSUMES_LINE = re.compile(r"^\s*(shows|assumes)\b", re.IGNORECASE)
_LEMMA_HEAD_LINE = re.compile(
    r"^(\s*)(lemma|corollary|proposition)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE,
)
_SORRY_ONLY = re.compile(r"^\s*sorry\s*\.?\s*$", re.IGNORECASE)
_PROOF_START_LINE = re.compile(
    r"^\s*(sorry|oops|proof\b|by\s|sledgehammer)\b",
    re.IGNORECASE,
)
_BEGIN_LINE = re.compile(r"^\s*begin\s*$", re.IGNORECASE)
_THEOREM_HEAD_LINE = re.compile(r"^\s*theorem\s+", re.IGNORECASE)
_USER_PROVIDE = "{{user provide}}"
_FORMAL_PROOF_SECTION_RE = re.compile(
    r"##\s*Formal\s+proof(?:\s+sketch)?\s*(.*)\Z", re.DOTALL | re.IGNORECASE
)
_SLEDGEHAMMER_LINE_RE = re.compile(r"\bsledgehammer\b")


def _fill_user_provide(
    user_template: str, replacements: list, prompt_path: str
) -> str:
    count = user_template.count(_USER_PROVIDE)
    if count != len(replacements):
        raise ValueError(
            f"提示词占位符数量与输入块数量不匹配: {prompt_path}, "
            f"占位符={count}, 输入块={len(replacements)}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(_USER_PROVIDE, block, 1)
    return out


def _clean_informal_proof(text: str) -> str:
    body = (text or "").strip()
    fence = _ISABELLE_FENCE_RE.search(body)
    if fence:
        body = (fence.group(1) or "").strip()
    body = re.sub(r"^\s*(?:informal\s+proof|proof\s+sketch|非形式化证明)\s*[:：]?\s*", "", body, flags=re.IGNORECASE)
    return body.strip()


def extract_formal_sketch_proof(raw: str) -> str:
    """从 2.2.2 形式化草图输出中提取证明体（去掉 ## Formal proof 段头与代码围栏）。"""
    text = (raw or "").strip()
    if not text:
        raise ValueError("形式化草图返回为空")
    m = _FORMAL_PROOF_SECTION_RE.search(text)
    section = m.group(1).strip() if m else text
    fence = _ISABELLE_FENCE_RE.search(section)
    code = fence.group(1).strip() if fence else section.strip()
    if not code:
        raise ValueError("形式化草图缺少证明体")
    proof_body = extract_sorry_replacement(code)
    lowered = proof_body.lower()
    if "sorry" in lowered or "oops" in lowered:
        raise ValueError("形式化草图证明体不得包含 sorry/oops")
    return proof_body


def default_lemma_proof_prompt_path() -> Path:
    return Path(__file__).resolve().parent / LEMMA_PROOF_PROMPT_FILENAME


def default_lemma_proof_repair_prompt_path() -> Path:
    return Path(__file__).resolve().parent / LEMMA_PROOF_REPAIR_PROMPT_FILENAME


def split_lemma_proof_prompt_file(text: str) -> Tuple[str, str]:
    """将 lemma_proof_prompt.txt 拆为 system（规则+示例）与 user（任务模板）。"""
    m = _LEMMA_PROOF_TASK_SPLIT.search(text)
    if not m:
        raise ValueError(
            "引理证明提示词中未找到分隔标记 '####below are your task'，"
            f"请检查 {LEMMA_PROOF_PROMPT_FILENAME}"
        )
    return text[: m.start()].strip(), text[m.start() :].strip()


def load_lemma_proof_prompt(prompt_path: str) -> Tuple[str, str]:
    path = Path(prompt_path)
    if not path.is_file():
        raise FileNotFoundError(f"引理证明 prompt 不存在: {path}")
    return split_lemma_proof_prompt_file(path.read_text(encoding="utf-8"))


def load_lemma_proof_repair_prompt(prompt_path: str) -> Tuple[str, str]:
    path = Path(prompt_path)
    if not path.is_file():
        raise FileNotFoundError(f"引理证明修复 prompt 不存在: {path}")
    return split_lemma_proof_prompt_file(path.read_text(encoding="utf-8"))


def extract_definitions_preamble(thy_text: str) -> str:
    """`begin` 之后、第一条 lemma/theorem 之前的定义与类型等（不含引理与主定理）。"""
    lines = thy_text.splitlines()
    begin_idx: Optional[int] = None
    for i, line in enumerate(lines):
        if _BEGIN_LINE.match(line):
            begin_idx = i
            break
    if begin_idx is None:
        return ""
    chunk: list[str] = []
    for line in lines[begin_idx + 1 :]:
        if _LEMMA_HEAD_LINE.match(line) or _THEOREM_HEAD_LINE.match(line):
            break
        chunk.append(line)
    return "\n".join(chunk).strip()


def lemma_statement_text(thy_text: str, lemma_name: str) -> str:
    """引理陈述：lemma 头与 fixes/assumes/shows，不含 sorry 与证明体。"""
    block = lemma_block_text(thy_text, lemma_name)
    if not block:
        return ""
    stmt_lines: list[str] = []
    for line in block.splitlines():
        if _PROOF_START_LINE.match(line):
            break
        stmt_lines.append(line)
    return "\n".join(stmt_lines).strip()


_BODY_START_LINE = re.compile(
    r"^\s*(?:proof|by|apply|using|unfolding|from|have|show|hence|thus|"
    r"moreover|ultimately|also|finally|let|obtain|consider|define|assume|"
    r"presume|note|fix|case|next|then|with|qed|done|defer|prefer|supply|"
    r"interpret|guess|sledgehammer|sorry|oops)\b"
)


def lemma_proof_body(thy_text: str, lemma_name: str) -> str:
    """提取引理块的证明体（去掉 lemma 头与 fixes/assumes/shows 陈述）。

    陈述行可能跨行（多行 assumes/shows），因此按“证明起始关键字”定位，
    而不是简单按行宽切分，避免丢掉以 using/from 开头的首行。
    """
    block = lemma_block_text(thy_text, lemma_name)
    if not block:
        return ""
    lines = block.splitlines()
    start = None
    for index, line in enumerate(lines[1:], start=1):
        if _BODY_START_LINE.match(line):
            start = index
            break
    if start is None:
        return ""
    body = lines[start:]
    while body and (not body[-1].strip() or body[-1].strip() == "end"):
        body.pop()
    return "\n".join(body).strip()


def build_lemma_proof_llm_context(
    thy_text: str, target_lemma_name: str
) -> tuple[str, str]:
    """组装 prompt：仅函数定义与待证引理陈述（单文件）。"""
    func_block = extract_definitions_preamble(thy_text).strip() or "(none)"
    target = lemma_statement_text(thy_text, target_lemma_name).strip() or "(none)"
    return func_block, target


def _collect_proven_ref_names(*texts: str) -> set[str]:
    """从引理陈述 / 证明体文本中收集可能引用 proven 库的事实名。"""
    refs: set[str] = set()
    for text in texts:
        if not (text or "").strip():
            continue
        refs |= _lemma_refs_in_block(text)
    return refs


def _proven_blocks_for_prompt(proven_text: str, *, ref_names: set[str]) -> list[str]:
    """按 proven 文件顺序返回 ref_names 命中的引理块（无命中则空）。"""
    if not ref_names or not (proven_text or "").strip():
        return []
    from ..eval.proof_difficulty_score_v2.thy_extract import extract_decl_blocks

    blocks = extract_decl_blocks(proven_text)
    return [
        blocks[name].strip()
        for name in blocks
        if name in ref_names and (blocks[name] or "").strip()
    ]


def build_lemma_proof_llm_context_from_files(
    context_thy_text: str,
    lemma_thy_text: str,
    target_lemma_name: str,
    *,
    context_thy_path: Optional[Path] = None,
    proven_lemmas_path: Optional[Path] = None,
    proven_filter_text: Optional[str] = None,
) -> tuple[str, str]:
    """
    组装 prompt：函数定义来自 *_defs.thy；proven 仅附加 proof/陈述中直接引用的子集
    （与 sketch_repair 一致，避免整库塞入 token）；引理陈述来自 unproven。
    """
    from ..lemma.unproven_lemma_store import UnprovenLemmaStore

    func_block = "(none)"
    if context_thy_path is not None:
        func_block = (
            UnprovenLemmaStore.read_defs_preamble_for_lemma_thy(
                context_thy_path
            ).strip()
            or "(none)"
        )
    else:
        func_block = extract_definitions_preamble(context_thy_text).strip() or "(none)"

    target = lemma_statement_text(lemma_thy_text, target_lemma_name).strip() or "(none)"

    if proven_lemmas_path is not None and proven_lemmas_path.is_file():
        ref_sources = [target]
        if proven_filter_text:
            ref_sources.append(proven_filter_text)
        ref_names = _collect_proven_ref_names(*ref_sources)
        proven_text = proven_lemmas_path.read_text(encoding="utf-8")
        proven_blocks = _proven_blocks_for_prompt(proven_text, ref_names=ref_names)
        if proven_blocks:
            from ..eval.proof_difficulty_score_v2.thy_extract import extract_decl_blocks

            total = len(extract_decl_blocks(proven_text))
            func_block = (
                f"{func_block}\n\n(* Proven lemmas referenced in proof *)\n"
                + "\n\n".join(proven_blocks)
            )
            logger.info(
                "引理 prompt proven 子集: %d/%d 条 (refs=%s)",
                len(proven_blocks),
                total,
                ", ".join(sorted(ref_names)[:12])
                + ("..." if len(ref_names) > 12 else ""),
            )

    return func_block, target


def fill_lemma_proof_user_template(
    user_template: str,
    function_definitions: str,
    lemma_statement: str,
    prompt_path: str,
) -> str:
    """填充首次证明任务模板（2 个 {{}}）。"""
    replacements = [
        (function_definitions or "").strip(),
        (lemma_statement or "").strip(),
    ]
    count = user_template.count(LEMMA_PROOF_PLACEHOLDER)
    if count != LEMMA_PROOF_PLACEHOLDERS:
        raise ValueError(
            f"引理证明 prompt 占位符 {LEMMA_PROOF_PLACEHOLDER!r} 应为 "
            f"{LEMMA_PROOF_PLACEHOLDERS} 个，实际 {count}: {prompt_path}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(LEMMA_PROOF_PLACEHOLDER, block, 1)
    return out


def format_lemma_with_failed_proof(
    lemma_statement: str, previous_proof: str
) -> str:
    """引理陈述 + 上一轮失败证明体（与 repair prompt 的 Lemma 节一致）。"""
    stmt = (lemma_statement or "").strip()
    proof = (previous_proof or "").strip()
    if not proof or proof == "(none)":
        return stmt or "(none)"
    if stmt and proof:
        return f"{stmt}\n{proof}"
    return proof or stmt or "(none)"


def fill_lemma_proof_repair_user_template(
    user_template: str,
    function_definitions: str,
    lemma_with_failed_proof: str,
    previous_strategy: str,
    isabelle_error: str,
    prompt_path: str,
) -> str:
    """填充修复任务模板（4 个 {{}}）：定义、引理+失败证明、思路、报错。"""
    replacements = [
        (function_definitions or "").strip(),
        (lemma_with_failed_proof or "").strip(),
        (previous_strategy or "").strip() or "(none)",
        (isabelle_error or "").strip() or "(none)",
    ]
    count = user_template.count(LEMMA_PROOF_PLACEHOLDER)
    if count != LEMMA_PROOF_REPAIR_PLACEHOLDERS:
        raise ValueError(
            f"引理证明修复 prompt 占位符 {LEMMA_PROOF_PLACEHOLDER!r} 应为 "
            f"{LEMMA_PROOF_REPAIR_PLACEHOLDERS} 个，实际 {count}: {prompt_path}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(LEMMA_PROOF_PLACEHOLDER, block, 1)
    return out


def extract_sorry_replacement(proof_text: str) -> str:
    """从 LLM 返回的引理/证明块中提取替换 sorry 的证明体。"""
    text = (proof_text or "").strip()
    if not text:
        raise ValueError("证明体为空")
    lines = text.splitlines()
    if len(lines) == 1 and lines[0].strip().lower().startswith(
        ("by ", "proof", "sledgehammer")
    ):
        return lines[0].strip()
    proof_lines: list[str] = []
    past_statement = False
    for line in lines:
        if _LEMMA_HEAD_LINE.match(line):
            past_statement = False
            continue
        if _SHOWS_ASSUMES_LINE.match(line):
            past_statement = True
            continue
        if not past_statement:
            continue
        if _SORRY_ONLY.match(line) or line.strip().lower() == "oops":
            continue
        proof_lines.append(line)
    body = "\n".join(proof_lines).strip()
    if body:
        return body
    start_idx: Optional[int] = None
    for i, line in enumerate(lines):
        s = line.strip()
        if s.lower().startswith(("by ", "proof")) or s == "sledgehammer":
            start_idx = i
            break
    if start_idx is not None:
        return "\n".join(lines[start_idx:]).strip()
    raise ValueError("无法从 LLM 输出中提取证明体")


def parse_lemma_proof_response(raw: str) -> Dict[str, Any]:
    """解析 ### Lemma proof + ### Proof strategy 或 ### Repair strategy。"""
    text = (raw or "").strip()
    if not text:
        raise ValueError("引理证明 LLM 返回为空")
    explanation = ""
    strat = _REPAIR_STRATEGY_SECTION_RE.search(text) or _PROOF_STRATEGY_SECTION_RE.search(
        text
    )
    if strat:
        explanation = strat.group(1).strip()
    proof_section = ""
    sec = _LEMMA_PROOF_SECTION_RE.search(text)
    if sec:
        proof_section = sec.group(1).strip()
    else:
        proof_section = text
    fence = _ISABELLE_FENCE_RE.search(proof_section)
    code = fence.group(1).strip() if fence else proof_section.strip()
    if not code:
        raise ValueError("缺少 ### Lemma proof 或 isabelle 代码块")
    proof_body = extract_sorry_replacement(code)
    if "sorry" in proof_body.lower() or "oops" in proof_body.lower():
        raise ValueError("证明体不得包含 sorry/oops")
    return {"proof": proof_body, "explanation": explanation}


def _lemma_refs_in_block(block: str) -> set[str]:
    refs = set(collect_lemma_refs_from_proof(block))
    for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_']*)\[OF\b", block):
        refs.add(m.group(1))
    return refs


def extract_thy_preamble(thy_text: str) -> str:
    """提取 theory 头部至首条 lemma/theorem 之前（含 begin、declare 等）。"""
    lines: list[str] = []
    for line in thy_text.splitlines():
        if _LEMMA_HEAD_LINE.match(line) or _THEOREM_HEAD_LINE.match(line):
            break
        lines.append(line)
    return "\n".join(lines).rstrip()


def build_single_lemma_verify_thy(
    unproven_path: Path,
    lemma_name: str,
    *,
    out_path: Optional[Path] = None,
) -> Path:
    """
    为单条引理构建最小验证用 .thy：preamble + 依赖闭包内的引理块 + 目标引理。
    避免每次 use_theories 加载整份 unproven_lemmas.thy。
    """
    text = unproven_path.read_text(encoding="utf-8")
    blocks = lemma_blocks_in_thy(text)
    if lemma_name not in blocks:
        raise ValueError(f"引理 {lemma_name} 不在 {unproven_path.name}")
    needed = expand_lemma_ref_closure(
        {lemma_name} | _lemma_refs_in_block(blocks[lemma_name]),
        blocks,
    )
    theory_stem = f"_verify_{lemma_name}"
    preamble = extract_thy_preamble(text)
    preamble_lines = preamble.splitlines()
    for i, line in enumerate(preamble_lines):
        if re.match(r"^\s*theory\s", line, re.IGNORECASE):
            preamble_lines[i] = f'theory "{theory_stem}"'
            break
    body_parts: list[str] = []
    for name, block in blocks.items():
        if name in needed and name != lemma_name:
            body_parts.append(block)
    body_parts.append(blocks[lemma_name])
    slice_text = "\n".join(preamble_lines) + "\n\n" + "\n".join(body_parts) + "\n\nend\n"
    target = out_path or (unproven_path.parent / f"{theory_stem}.thy")
    target.write_text(slice_text, encoding="utf-8")
    return target


def _lemma_proof_accepted_on_slice(
    code: int,
    verify_out: str,
    slice_path: Path,
    lemma_thy_path: Path,
    lemma_name: str,
    lemma_text: str,
) -> bool:
    """单引理切片验证通过：整体无致命错误，原 unproven 中该引理已证，切片内无该引理块报错。"""
    if not _verification_passed(code, verify_out):
        return False
    if not _lemma_verified_in_thy(lemma_text, lemma_name):
        return False
    slice_text = slice_path.read_text(encoding="utf-8")
    if _unproven_errors_in_lemma_block(
        verify_out, slice_path, lemma_name, slice_text
    ):
        return False
    return True


def verify_single_lemma_light(
    lemma_thy_path: Path,
    lemma_name: str,
    config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> Tuple[bool, str]:
    """在最小切片 .thy 上验证单条引理，不重启 session。"""
    slice_path = build_single_lemma_verify_thy(lemma_thy_path, lemma_name)
    n_lines = len(slice_path.read_text(encoding="utf-8").splitlines())
    print(
        f"    [lemma-light] {lemma_name} 切片验证 "
        f"({slice_path.name}, {n_lines} 行)...",
        flush=True,
    )

    def _run(pool: IsabelleServerSessionPool) -> Tuple[bool, str]:
        code, out = _run_use_thy(
            slice_path,
            config,
            tag="lemma_single_verify",
            server_pool=pool,
        )
        lemma_text = lemma_thy_path.read_text(encoding="utf-8")
        ok = _lemma_proof_accepted_on_slice(
            code, out, slice_path, lemma_thy_path, lemma_name, lemma_text
        )
        return ok, out

    if server_pool is not None and server_pool.is_active:
        return _run(server_pool)
    with IsabelleServerSessionPool(config) as pool:
        return _run(pool)


def lemma_block_text(thy_text: str, lemma_name: str) -> str:
    lines = thy_text.splitlines()
    block: list[str] = []
    active = False
    for line in lines:
        m = _LEMMA_HEAD_LINE.match(line)
        if m:
            if active:
                break
            active = m.group(3) == lemma_name
            if active:
                block.append(line)
            continue
        if active:
            if _LEMMA_HEAD_LINE.match(line):
                break
            block.append(line)
    return "\n".join(block)


def _normalize_proof_lines(proof_body: str, base_indent: str = "  ") -> list[str]:
    body = (proof_body or "").strip().replace("\\n", "\n")
    lines = body.splitlines()
    if len(lines) == 1 and not lines[0].strip().lower().startswith("proof"):
        stripped = lines[0].strip()
        if stripped.startswith("by ") or stripped == "sledgehammer":
            return [f"{base_indent}{stripped}"]
    out: list[str] = []
    for ln in lines:
        if ln.strip():
            out.append(ln if ln.startswith((" ", "\t")) else f"{base_indent}{ln}")
        else:
            out.append("")
    return out


def _lemma_line_span_1based(thy_text: str, lemma_name: str) -> Optional[Tuple[int, int]]:
    """返回引理块在 .thy 中的 1-based 起止行号（含 lemma 头与 proof 体）。"""
    lines = thy_text.splitlines()
    start: Optional[int] = None
    for i, line in enumerate(lines, 1):
        m = _LEMMA_HEAD_LINE.match(line)
        if m:
            if start is not None:
                return start, i - 1
            if m.group(3) == lemma_name:
                start = i
            continue
        if start is not None and re.match(r"^\s*theorem\s+", line, re.IGNORECASE):
            return start, i - 1
    if start is None:
        return None
    return start, len(lines)


def _unproven_errors_in_lemma_block(
    verify_out: str,
    unproven_path: Path,
    lemma_name: str,
    unproven_text: str,
) -> list[tuple[int, str]]:
    """从 Isabelle 输出中提取落在目标引理行范围内的 unproven 文件 error 消息。"""
    span = _lemma_line_span_1based(unproven_text, lemma_name)
    if not span or not verify_out:
        return []
    start, end = span
    errors: list[tuple[int, str]] = []
    for msg, line_no, _fpath in iter_isabelle_server_error_messages(
        verify_out, file_filter=str(unproven_path)
    ):
        if start <= line_no <= end:
            errors.append((line_no, msg))
    return errors


def _lemma_proof_accepted(
    code: int,
    verify_out: str,
    lemma_thy_path: Path,
    lemma_name: str,
    lemma_text: str,
) -> bool:
    """引理证明成功：整体验证通过，且 unproven 中该引理块无 Isabelle 报错。"""
    if not _verification_passed(code, verify_out):
        return False
    if not _lemma_verified_in_thy(lemma_text, lemma_name):
        return False
    if _unproven_errors_in_lemma_block(
        verify_out, lemma_thy_path, lemma_name, lemma_text
    ):
        return False
    return True


def apply_lemma_proof_to_thy(
    thy_path: Path,
    lemma_name: str,
    proof_body: str,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> None:
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    in_lemma = False
    sorry_idx: Optional[int] = None
    for i, line in enumerate(lines):
        m = _LEMMA_HEAD_LINE.match(line)
        if m:
            if in_lemma and sorry_idx is None:
                break
            in_lemma = m.group(3) == lemma_name
            continue
        if in_lemma and _SORRY_ONLY.match(line):
            sorry_idx = i
            break
        if in_lemma and _LEMMA_HEAD_LINE.match(line):
            break
    if sorry_idx is None:
        raise ValueError(f"引理 {lemma_name} 未找到 sorry 行")
    indent = re.match(r"^(\s*)", lines[sorry_idx]).group(1) or "  "
    new_lines = _normalize_proof_lines(proof_body, indent if indent else "  ")
    lines = lines[:sorry_idx] + new_lines + lines[sorry_idx + 1 :]
    thy_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    from ..lemma.proven_lemma_store import ProvenLemmaStore

    ProvenLemmaStore.normalize_thy_file(thy_path)
    _mark_thy_disk_changed(server_pool)


def reset_lemma_to_sorry(
    thy_path: Path,
    lemma_name: str,
    original_block: str,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> None:
    lines = thy_path.read_text(encoding="utf-8").splitlines()
    start_idx: Optional[int] = None
    end_idx: Optional[int] = None
    for i, line in enumerate(lines):
        m = _LEMMA_HEAD_LINE.match(line)
        if m and m.group(3) == lemma_name:
            start_idx = i
            continue
        if start_idx is not None and end_idx is None:
            if _LEMMA_HEAD_LINE.match(line) or re.match(
                r"^\s*theorem\s+", line, re.IGNORECASE
            ):
                end_idx = i
                break
    if start_idx is None:
        raise ValueError(f"未找到引理 {lemma_name}")
    if end_idx is None:
        end_idx = len(lines)
    new_lines = (
        lines[:start_idx]
        + original_block.strip().splitlines()
        + lines[end_idx:]
    )
    thy_path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
    from ..lemma.proven_lemma_store import ProvenLemmaStore

    ProvenLemmaStore.normalize_thy_file(thy_path)
    _mark_thy_disk_changed(server_pool)


def _lemma_verified_in_thy(thy_text: str, lemma_name: str) -> bool:
    block = lemma_block_text(thy_text, lemma_name)
    if not block or lemma_still_sorry(block):
        return False
    return "sledgehammer" not in block.lower()


def try_sledgehammer_repair_lemma(
    lemma_thy_path: Path,
    lemma_name: str,
    isabelle_config: IsabelleRunnerConfig,
    verify_output: str,
    *,
    verify_thy_path: Optional[Path] = None,
    server_pool: Optional[IsabelleServerSessionPool] = None,
    light_verify: bool = False,
) -> Tuple[bool, str]:
    """
    修复阶段优先：在 unproven_lemmas.thy 中保留失败证明并做定向 sledgehammer；
    整体验证在 verify_thy_path（默认 unproven_lemmas.thy）上执行。
    """
    if not isabelle_config.repair_failed_steps:
        return False, verify_output

    verify_target = verify_thy_path or lemma_thy_path

    print(
        f"    [lemma-sh] {lemma_name} 尝试 sledgehammer 修复失败证明步 ...",
        flush=True,
    )
    logs: list[str] = []

    def _run(pool: IsabelleServerSessionPool) -> Tuple[bool, str]:
        repairs, repair_out = _repair_failed_steps_with_sledgehammer(
            lemma_thy_path,
            isabelle_config,
            verify_output,
            logs,
            server_pool=pool,
        )
        if repairs == 0:
            print(
                f"    [lemma-sh] {lemma_name} sledgehammer 未回填任何步骤，"
                f"跳过整体验证，进入 LLM 修复",
                flush=True,
            )
            return False, repair_out or verify_output
        prepare_session_for_repair_final_verify(pool)
        lemma_text = lemma_thy_path.read_text(encoding="utf-8")
        if light_verify:
            slice_path = build_single_lemma_verify_thy(lemma_thy_path, lemma_name)
            code, out = _run_use_thy(
                slice_path,
                isabelle_config,
                tag="lemma_single_verify",
                server_pool=pool,
            )
            ok = _lemma_proof_accepted_on_slice(
                code, out, slice_path, lemma_thy_path, lemma_name, lemma_text
            )
        else:
            code, out = _run_use_thy(
                verify_target,
                isabelle_config,
                tag="lemma_sledgehammer_repair_verify",
                server_pool=pool,
            )
            ok = _lemma_proof_accepted(
                code, out, lemma_thy_path, lemma_name, lemma_text
            )
        return ok, out

    if server_pool is not None and server_pool.is_active:
        return _run(server_pool)
    with IsabelleServerSessionPool(isabelle_config) as pool:
        return _run(pool)


def verify_then_sledgehammer(
    thy_path: Path,
    config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
    lemma_thy_path: Optional[Path] = None,
    lemma_name: Optional[str] = None,
    light_verify: bool = False,
) -> Tuple[bool, str]:
    """
    在 thy_path 上加载理论以检查引理/定理状态。

    引理迭代阶段（lemma_name 已设）：在 unproven_lemmas.thy 上 use_theories，
    仅判定当前引理是否通过；失败时由 try_sledgehammer_repair_lemma 在同文件
    上修复，报错行号与修复目标一致。无 lemma_name 时用于 sketch 等整体验证。

    light_verify=True 时在最小切片 .thy 上验证，不重启 session，避免整文件加载卡顿。
    """

    def _run(pool: IsabelleServerSessionPool) -> Tuple[bool, str]:
        lemma_thy = lemma_thy_path or thy_path
        lemma_text = lemma_thy.read_text(encoding="utf-8")
        if light_verify and lemma_name:
            slice_path = build_single_lemma_verify_thy(lemma_thy, lemma_name)
            n_lines = len(slice_path.read_text(encoding="utf-8").splitlines())
            print(
                f"    [lemma-light] {lemma_name} 切片验证 "
                f"({slice_path.name}, {n_lines} 行)...",
                flush=True,
            )
            code, out = _run_use_thy(
                slice_path,
                config,
                tag="lemma_single_verify",
                server_pool=pool,
            )
            if _lemma_proof_accepted_on_slice(
                code, out, slice_path, lemma_thy, lemma_name, lemma_text
            ):
                return True, out
            return False, out
        prepare_session_for_lemma_proof_verify(pool)
        code, out = _run_use_thy(
            thy_path, config, tag="lemma_proof_verify", server_pool=pool
        )
        if lemma_name and _lemma_proof_accepted(
            code, out, lemma_thy, lemma_name, lemma_text
        ):
            return True, out
        if (
            lemma_name
            and _is_stuck_verify_output(out)
            and config.repair_failed_steps
        ):
            print(
                f"    [lemma-stuck] {lemma_name} verify 超时，尝试 sledgehammer 替换卡住证明步 ...",
                flush=True,
            )
            _repair_stuck_verify_with_sledgehammer(
                lemma_thy, config, out, [], server_pool=pool
            )
            prepare_session_for_repair_final_verify(pool)
            code, out = _run_use_thy(
                thy_path, config, tag="lemma_proof_verify", server_pool=pool
            )
            if _lemma_proof_accepted(
                code, out, lemma_thy, lemma_name, lemma_text
            ):
                return True, out
        if lemma_name:
            return False, out
        if _verification_passed(code, out):
            return True, out
        processed = process_sledgehammer_and_verify(
            str(thy_path), config, server_pool=pool
        )
        out = processed.get("verify_output") or out
        ok = bool(processed.get("success"))
        return ok, out

    if server_pool is not None and server_pool.is_active:
        return _run(server_pool)
    with IsabelleServerSessionPool(config) as pool:
        return _run(pool)


class LemmaProofIterator:
    def __init__(self, config: BLProverConfig, llm: LLMInterface):
        self.config = config
        self.llm = llm
        path = config.lemma_proof_prompt_path or str(default_lemma_proof_prompt_path())
        self._prompt_path = path
        self._system_prompt, self._user_template = load_lemma_proof_prompt(path)
        repair_path = config.lemma_proof_repair_prompt_path or str(
            default_lemma_proof_repair_prompt_path()
        )
        self._repair_prompt_path = repair_path
        self._repair_system_prompt, self._repair_user_template = (
            load_lemma_proof_repair_prompt(repair_path)
        )
        # 论文 2.5：引理证明复用 2.2.1 非形式化证明与 2.2.2 形式化草图模板
        self._two_stage_enabled = bool(getattr(config, "lemma_two_stage_enabled", True))
        self._informal_prompt_path = config.theorem_to_informal_prompt_path
        self._formal_prompt_path = config.informal_to_formal_prompt_path
        # 隐藏的完整证明提示词优先；旧 step4 提示词保持原样，仅作回退。
        if HIDDEN_FULL_PROOF_PROMPT.is_file():
            self._formal_prompt_path = str(HIDDEN_FULL_PROOF_PROMPT)
        self._informal_system_prompt = ""
        self._informal_user_template = ""
        self._formal_system_prompt = ""
        self._formal_user_template = ""
        if self._two_stage_enabled:
            try:
                from ..sketch.construct_lemma_generator import (
                    split_construct_lemma_prompt_file,
                )

                self._informal_system_prompt, self._informal_user_template = (
                    split_construct_lemma_prompt_file(
                        Path(self._informal_prompt_path).read_text(encoding="utf-8")
                    )
                )
                self._formal_system_prompt, self._formal_user_template = (
                    split_construct_lemma_prompt_file(
                        Path(self._formal_prompt_path).read_text(encoding="utf-8")
                    )
                )
            except Exception as exc:  # 模板不可用时退回单阶段
                logger.warning("引理两阶段模板加载失败，退回单阶段: %s", exc)
                self._two_stage_enabled = False

    def _run_llm_verify_round(
        self,
        lemma_thy_path: Path,
        verify_thy_path: Path,
        lemma_name: str,
        isabelle_config: IsabelleRunnerConfig,
        *,
        user_prompt: str,
        sys_prompt: str,
        prompt_kind: str,
        initial_round: int,
        repair_round: int,
        server_pool: Optional[IsabelleServerSessionPool] = None,
        light_verify: bool = False,
    ) -> Dict[str, Any]:
        """单次 LLM 调用 → 解析 → 写入 unproven .thy → 在 unproven 上验证该引理。"""
        attempt_rec: Dict[str, Any] = {
            "prompt_kind": prompt_kind,
            "initial_round": initial_round,
            "repair_round": repair_round,
            "llm_raw_length": 0,
            "success": False,
        }
        raw = self.llm.generate(user_prompt, sys_prompt)
        attempt_rec["llm_raw_length"] = len(raw or "")
        try:
            parsed = parse_lemma_proof_response(raw)
        except ValueError as exc:
            attempt_rec["error"] = f"llm_parse: {exc}"
            attempt_rec["last_error"] = str(exc)
            return attempt_rec
        return self._apply_and_verify(
            lemma_thy_path,
            verify_thy_path,
            lemma_name,
            isabelle_config,
            proof_body=str(parsed.get("proof", "")).strip(),
            explanation=str(parsed.get("explanation", "")).strip(),
            attempt_rec=attempt_rec,
            server_pool=server_pool,
            light_verify=light_verify,
        )

    def _apply_and_verify(
        self,
        lemma_thy_path: Path,
        verify_thy_path: Path,
        lemma_name: str,
        isabelle_config: IsabelleRunnerConfig,
        *,
        proof_body: str,
        explanation: str,
        attempt_rec: Dict[str, Any],
        server_pool: Optional[IsabelleServerSessionPool] = None,
        light_verify: bool = False,
    ) -> Dict[str, Any]:
        """写入证明体 ->（必要时回填 sledgehammer 占位）-> 在该引理上验证。"""
        attempt_rec["explanation"] = explanation
        try:
            apply_lemma_proof_to_thy(
                lemma_thy_path,
                lemma_name,
                proof_body,
                server_pool=server_pool,
            )
            attempt_rec["applied_proof"] = proof_body
        except ValueError as exc:
            attempt_rec["error"] = f"llm_parse: {exc}"
            attempt_rec["last_error"] = str(exc)
            return attempt_rec

        # 论文 2.2.2 的草图以 sledgehammer 占位；先回填占位行再判定该引理
        if _SLEDGEHAMMER_LINE_RE.search(proof_body):
            print(
                f"    [lemma-two-stage] {lemma_name} 回填 sledgehammer 占位符 ...",
                flush=True,
            )
            process_sledgehammer_and_verify(
                str(lemma_thy_path), isabelle_config, server_pool=server_pool
            )

        ok, verify_out = verify_then_sledgehammer(
            verify_thy_path,
            isabelle_config,
            server_pool=server_pool,
            lemma_thy_path=lemma_thy_path,
            lemma_name=lemma_name,
            light_verify=light_verify,
        )
        attempt_rec["verify_after_sledgehammer"] = ok
        if ok:
            attempt_rec["success"] = True
            return attempt_rec

        attempt_rec["last_error"] = verify_out
        attempt_rec["isabelle_error_preview"] = (verify_out or "")[:1500]
        return attempt_rec

    def _run_two_stage_verify_round(
        self,
        lemma_thy_path: Path,
        verify_thy_path: Path,
        lemma_name: str,
        isabelle_config: IsabelleRunnerConfig,
        *,
        func_defs: str,
        lemma_statement: str,
        initial_round: int,
        server_pool: Optional[IsabelleServerSessionPool] = None,
        light_verify: bool = False,
    ) -> Dict[str, Any]:
        """论文 2.5：先 2.2.1 生成非形式化证明，再 2.2.2 生成完整形式化证明。"""
        attempt_rec: Dict[str, Any] = {
            "prompt_kind": "two_stage",
            "initial_round": initial_round,
            "repair_round": 0,
            "llm_raw_length": 0,
            "success": False,
        }
        try:
            informal_user = _fill_user_provide(
                self._informal_user_template,
                [func_defs, lemma_statement],
                self._informal_prompt_path,
            )
            informal_raw = self.llm.generate(informal_user, self._informal_system_prompt)
            informal_proof = _clean_informal_proof(informal_raw)
            if not informal_proof:
                raise ValueError("非形式化证明为空")
            attempt_rec["informal_proof_length"] = len(informal_proof)

            sketch_replacements = [func_defs, lemma_statement, informal_proof]
            if self._formal_user_template.count(_USER_PROVIDE) >= 4:
                try:
                    blocks = lemma_blocks_in_thy(
                        lemma_thy_path.read_text(encoding="utf-8")
                    )
                except OSError:
                    blocks = {}
                other_lemmas = "\n\n".join(
                    block for name, block in blocks.items() if name != lemma_name
                )
                sketch_replacements.append(other_lemmas.strip() or "(none)")
            sketch_user = _fill_user_provide(
                self._formal_user_template,
                sketch_replacements,
                self._formal_prompt_path,
            )
            sketch_raw = self.llm.generate(sketch_user, self._formal_system_prompt)
            attempt_rec["llm_raw_length"] = len(sketch_raw or "")
            proof_body = extract_formal_sketch_proof(sketch_raw)
            explanation = informal_proof[:600]
        except ValueError as exc:
            attempt_rec["error"] = f"two_stage: {exc}"
            attempt_rec["last_error"] = str(exc)
            return attempt_rec

        return self._apply_and_verify(
            lemma_thy_path,
            verify_thy_path,
            lemma_name,
            isabelle_config,
            proof_body=proof_body,
            explanation=explanation,
            attempt_rec=attempt_rec,
            server_pool=server_pool,
            light_verify=light_verify,
        )

    def prove_one_lemma(
        self,
        lemma_thy_path: Path,
        lemma_name: str,
        original_block: str,
        isabelle_config: IsabelleRunnerConfig,
        *,
        verify_thy_path: Optional[Path] = None,
        context_thy_path: Optional[Path] = None,
        proven_lemmas_path: Optional[Path] = None,
        max_initial: Optional[int] = None,
        max_repair: Optional[int] = None,
        server_pool: Optional[IsabelleServerSessionPool] = None,
        light_verify: bool = False,
    ) -> Dict[str, Any]:
        """
        两阶段证明单条引理（写入并在 unproven_lemmas.thy 上验证）：
        - 首次：lemma_proof_prompt（函数定义 + 引理陈述），最多 max_initial 轮；
        - 每轮首次验证失败后：先 sledgehammer，再 LLM 修复，最多 max_repair 轮；
        - 修复仍失败则回到首次重新生成，直至首轮次数用尽。
        """
        verify_thy = verify_thy_path or lemma_thy_path
        context_thy = context_thy_path or verify_thy
        max_initial = (
            max_initial
            if max_initial is not None
            else self.config.used_lemma_initial_max_attempts
        )
        max_repair = (
            max_repair
            if max_repair is not None
            else self.config.used_lemma_repair_max_attempts
        )
        record: Dict[str, Any] = {
            "lemma_name": lemma_name,
            "success": False,
            "max_initial_attempts": max_initial,
            "max_repair_attempts": max_repair,
            "attempts": [],
        }

        for initial_round in range(1, max_initial + 1):
            reset_lemma_to_sorry(
                lemma_thy_path,
                lemma_name,
                original_block,
                server_pool=server_pool,
            )
            lemma_text = lemma_thy_path.read_text(encoding="utf-8")
            context_text = context_thy.read_text(encoding="utf-8")
            func_defs, target_block = build_lemma_proof_llm_context_from_files(
                context_text,
                lemma_text,
                lemma_name,
                context_thy_path=context_thy,
                proven_lemmas_path=proven_lemmas_path,
            )
            target = target_block or lemma_statement_text(lemma_text, lemma_name)

            if self._two_stage_enabled:
                print(
                    f"    [lemma-two-stage] {lemma_name} 非形式化证明 → 形式化草图"
                    f"（首次 {initial_round}/{max_initial}）...",
                    flush=True,
                )
                initial_rec = self._run_two_stage_verify_round(
                    lemma_thy_path,
                    verify_thy,
                    lemma_name,
                    isabelle_config,
                    func_defs=func_defs,
                    lemma_statement=target,
                    initial_round=initial_round,
                    server_pool=server_pool,
                    light_verify=light_verify,
                )
            else:
                print(
                    f"    [lemma-llm] {lemma_name} 首次 {initial_round}/{max_initial} ...",
                    flush=True,
                )
                initial_rec = self._run_llm_verify_round(
                    lemma_thy_path,
                    verify_thy,
                    lemma_name,
                    isabelle_config,
                    user_prompt=fill_lemma_proof_user_template(
                        self._user_template,
                        func_defs,
                        target,
                        self._prompt_path,
                    ),
                    sys_prompt=self._system_prompt,
                    prompt_kind="initial",
                    initial_round=initial_round,
                    repair_round=0,
                    server_pool=server_pool,
                    light_verify=light_verify,
                )
            record["attempts"].append(initial_rec)
            if initial_rec.get("success"):
                record["success"] = True
                return record

            previous_proof = str(initial_rec.get("applied_proof", "")).strip()
            previous_strategy = str(initial_rec.get("explanation", "")).strip()
            last_error = str(initial_rec.get("last_error", ""))

            if not previous_proof:
                continue

            for repair_round in range(1, max_repair + 1):
                # 保留 unproven .thy 中上一轮失败证明，先 sledgehammer，再 LLM
                sh_ok, sh_out = try_sledgehammer_repair_lemma(
                    lemma_thy_path,
                    lemma_name,
                    isabelle_config,
                    last_error,
                    verify_thy_path=verify_thy,
                    server_pool=server_pool,
                    light_verify=light_verify,
                )
                sh_rec: Dict[str, Any] = {
                    "prompt_kind": "sledgehammer",
                    "initial_round": initial_round,
                    "repair_round": repair_round,
                    "success": sh_ok,
                    "verify_after_sledgehammer": sh_ok,
                }
                if sh_out:
                    sh_rec["isabelle_error_preview"] = sh_out[:1500]
                    sh_rec["last_error"] = sh_out
                record["attempts"].append(sh_rec)
                if sh_ok:
                    # sledgehammer 修复是就地改写文件，成功证明只存在于 .thy 中；
                    # 必须回填到记录里，供 unused 互斥重置后的统一恢复使用。
                    try:
                        sh_rec["applied_proof"] = lemma_proof_body(
                            lemma_thy_path.read_text(encoding="utf-8"),
                            lemma_name,
                        )
                    except OSError:
                        pass
                    record["success"] = True
                    return record
                last_error = sh_out

                prepare_session_for_lemma_llm_repair(server_pool)

                reset_lemma_to_sorry(
                    lemma_thy_path,
                    lemma_name,
                    original_block,
                    server_pool=server_pool,
                )
                err_text = (
                    format_isabelle_error_for_prompt(last_error) if last_error else ""
                )
                lemma_failed = format_lemma_with_failed_proof(
                    target, previous_proof
                )
                func_defs_repair, _ = build_lemma_proof_llm_context_from_files(
                    context_text,
                    lemma_text,
                    lemma_name,
                    context_thy_path=context_thy,
                    proven_lemmas_path=proven_lemmas_path,
                    proven_filter_text=lemma_failed,
                )
                print(
                    f"    [lemma-llm] {lemma_name} 大模型修复 {repair_round}/{max_repair} "
                    f"(首次 {initial_round}/{max_initial}) ...",
                    flush=True,
                )
                repair_rec = self._run_llm_verify_round(
                    lemma_thy_path,
                    verify_thy,
                    lemma_name,
                    isabelle_config,
                    user_prompt=fill_lemma_proof_repair_user_template(
                        self._repair_user_template,
                        func_defs_repair,
                        lemma_failed,
                        previous_strategy,
                        err_text,
                        self._repair_prompt_path,
                    ),
                    sys_prompt=self._repair_system_prompt,
                    prompt_kind="repair",
                    initial_round=initial_round,
                    repair_round=repair_round,
                    server_pool=server_pool,
                    light_verify=light_verify,
                )
                record["attempts"].append(repair_rec)
                if repair_rec.get("success"):
                    record["success"] = True
                    return record

                last_error = str(repair_rec.get("last_error", ""))
                if repair_rec.get("applied_proof"):
                    previous_proof = str(repair_rec["applied_proof"]).strip()
                if repair_rec.get("explanation"):
                    previous_strategy = str(repair_rec["explanation"]).strip()

        record["error"] = "max_initial_attempts_exceeded"
        return record


def summarize_lemma_proof_result(record: Dict[str, Any]) -> str:
    """将 prove_one_lemma 返回结构整理为单行结果说明（供控制台输出）。"""
    name = str(record.get("lemma_name") or "?")
    if record.get("success"):
        for att in reversed(record.get("attempts") or []):
            if not att.get("success"):
                continue
            kind = str(att.get("prompt_kind") or "")
            initial_round = int(att.get("initial_round") or 0)
            repair_round = int(att.get("repair_round") or 0)
            if kind == "initial":
                return (
                    f"{name} 证明成功（LLM 首次 {initial_round}/"
                    f"{record.get('max_initial_attempts', '?')}）"
                )
            if kind == "sledgehammer":
                return (
                    f"{name} 证明成功（sledgehammer 修复 {repair_round}/"
                    f"{record.get('max_repair_attempts', '?')}，"
                    f"首次轮 {initial_round}）"
                )
            if kind == "repair":
                return (
                    f"{name} 证明成功（LLM 修复 {repair_round}/"
                    f"{record.get('max_repair_attempts', '?')}，"
                    f"首次轮 {initial_round}）"
                )
        return f"{name} 证明成功"

    attempts = record.get("attempts") or []
    max_initial = record.get("max_initial_attempts", "?")
    n = len(attempts)
    err = str(record.get("error") or "")
    if err == "max_initial_attempts_exceeded":
        return (
            f"{name} 证明失败（{max_initial} 轮首次尝试已用尽，共 {n} 次验证）"
        )
    last_err = ""
    for att in reversed(attempts):
        preview = str(att.get("isabelle_error_preview") or att.get("last_error") or "")
        if preview:
            last_err = preview.splitlines()[0][:120]
            break
    if last_err:
        return f"{name} 证明失败（共 {n} 次验证；末次: {last_err}）"
    return f"{name} 证明失败（共 {n} 次验证）"
