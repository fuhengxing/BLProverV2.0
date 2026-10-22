"""
论文 2.3.3：修复引理构造策略 + 引理修正机制（图 2-9 ~ 2-12）。

- 修复引理构造策略：输入 函数定义 / 定理陈述 / 带断裂点标记 (*@>>> lemma <<< *) 的形式化证明
  / Isabelle 错误信息，输出 sorry 占位的修复引理。
- 引理修正机制：修复引理未通过验证时，额外输入"先前失败的引理"，诊断失败根因并产出修正版。

本模块只负责：断裂点定位与标记、提示词块组装、模型输出解析，以及"构造 -> 合并 -> 重验 ->
失败则修正"的回路编排；Isabelle 的重新验证通过 verify_callback 注入，便于单测。
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, List, Optional, Tuple

from ..lemma.unproven_lemma_store import UnprovenLemmaStore
from ..utils.isabelle_sledgehammer import (
    _extract_error_positions,
    _is_repairable_proof_error,
    format_isabelle_error_for_prompt,
)

logger = logging.getLogger(__name__)

BREAK_MARKER = "(*@>>> lemma <<< *)"

_FENCE_RE = re.compile(r"```(?:isabelle)?[ \t]*\r?\n?(.*?)```", re.DOTALL | re.IGNORECASE)
_THOUGHTS_PREFIX_RE = re.compile(r"^\s*Thoughts\s*:\s*", re.IGNORECASE)
_LINEAR_LABEL_RE = re.compile(
    r"^\s*Linear\s*label\s*:\s*(.*)$", re.IGNORECASE | re.MULTILINE
)
_HEADER_LINE_RE = re.compile(
    r"^\s*(theory|imports|begin|end|declare|section|subsection|text)\b"
)
_BODY_HEADER_RE = re.compile(
    r"^\s*theory\s.*?\bbegin\b\s*", re.DOTALL | re.IGNORECASE
)


def _strip_marker(line: str) -> str:
    return line.replace(BREAK_MARKER, "").rstrip()


def pick_break_line(thy_text: str, verify_output: str) -> Optional[int]:
    """从 Isabelle 报错中定位证明断裂点所在行（1-based）。"""
    lines = (thy_text or "").splitlines()
    if not lines:
        return None
    positions = _extract_error_positions(verify_output or "")
    ordered = [(ln, msg) for ln, msg in positions if _is_repairable_proof_error(msg)]
    ordered += [(ln, msg) for ln, msg in positions if (ln, msg) not in ordered]
    for line_no, _msg in ordered:
        if not (1 <= line_no <= len(lines)):
            continue
        stripped = _strip_marker(lines[line_no - 1]).strip()
        if stripped and not stripped.startswith("(*") and not _HEADER_LINE_RE.match(stripped):
            return line_no
    # 回退：最后一个可标记的证明行
    for idx in range(len(lines) - 1, -1, -1):
        stripped = _strip_marker(lines[idx]).strip()
        if not stripped or stripped.startswith("(*"):
            continue
        if _HEADER_LINE_RE.match(stripped):
            continue
        return idx + 1
    return None


def inject_break_marker(thy_text: str, line_no: int) -> str:
    """在指定行末尾插入断裂点标记（论文 2.3.3 图 2-9）。"""
    text = thy_text or ""
    lines = text.splitlines()
    if not (1 <= line_no <= len(lines)):
        return text
    line = lines[line_no - 1]
    if BREAK_MARKER in line:
        return text
    lines[line_no - 1] = _strip_marker(line) + "  " + BREAK_MARKER
    out = "\n".join(lines)
    if text.endswith("\n"):
        out += "\n"
    return out


def extract_theory_body(thy_text: str) -> str:
    """去掉 theory/imports/begin 头与结尾 end，返回可放入提示词的证明正文。"""
    text = (thy_text or "").strip()
    if not text:
        return ""
    m = _BODY_HEADER_RE.search(text)
    if m:
        text = text[m.end():]
    lines = text.splitlines()
    while lines and lines[-1].strip() == "end":
        lines.pop()
    while lines and lines[0].strip().startswith("declare"):
        lines.pop(0)
    return "\n".join(lines).strip()


def _extract_linear_label(preamble: str) -> str:
    """从模型输出的前置文本中提取线性标签（方案 C）。"""
    for line in (preamble or "").splitlines():
        m = _LINEAR_LABEL_RE.match(line)
        if m:
            return m.group(1).strip()
    return ""


def parse_lemmas_with_thoughts(raw_text: str) -> List[Dict[str, str]]:
    """解析模型输出：每个 ```isabelle``` 引理块 + 其前置 Thoughts。"""
    raw = raw_text or ""
    results: List[Dict[str, str]] = []
    cursor = 0
    for m in _FENCE_RE.finditer(raw):
        body = (m.group(1) or "").strip()
        preamble = raw[cursor:m.start()]
        cursor = m.end()
        thoughts = _THOUGHTS_PREFIX_RE.sub("", (preamble or "").strip()).strip()
        linear_label = _extract_linear_label(preamble)
        for name, block in UnprovenLemmaStore.parse_extra_lemma_blocks(body).items():
            results.append(
                {
                    "name": name,
                    "statement": block,
                    "thoughts": thoughts,
                    "linear_label": linear_label,
                }
            )
    if results:
        return results
    # 回退：模型未使用代码围栏时，直接解析裸引理声明
    for name, block in UnprovenLemmaStore.parse_extra_lemma_blocks(raw).items():
        results.append(
            {"name": name, "statement": block, "thoughts": "", "linear_label": ""}
        )
    return results


def format_previous_lemma_block(lemma: Dict[str, str]) -> str:
    """按图 2-11/2-12 的 '## Previous lemma' 格式组装上一条失败引理。"""
    thoughts = (lemma.get("thoughts") or "").strip()
    statement = (lemma.get("statement") or "").strip()
    parts: List[str] = []
    if thoughts:
        parts.append(f"Thoughts: {thoughts}")
    if statement:
        parts.append("```isabelle\n" + statement + "\n```")
    return "\n".join(parts).strip() or "(none)"


def _fill_user_provide(user_template: str, replacements: List[str]) -> str:
    placeholder = "{{user provide}}"
    count = user_template.count(placeholder)
    if count != len(replacements):
        raise ValueError(
            f"提示词占位符数量与输入块数量不匹配: 占位符={count}, 输入块={len(replacements)}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(placeholder, block, 1)
    return out


@dataclass
class RepairLemmaContext:
    theorem_name: str
    theorem_data: Dict
    theory_file: Path
    theory_dir: Path
    result_dir: Path
    unproven_thy_path: Path
    verify_output: str
    repair_prompt_path: str
    revision_prompt_path: str
    max_attempts: int = 3


@dataclass
class RepairLemmaResult:
    success: bool = False
    attempts: int = 0
    marker_line: Optional[int] = None
    lemmas: List[Dict[str, str]] = field(default_factory=list)
    merged_names: List[str] = field(default_factory=list)
    linear_labels: Dict[str, str] = field(default_factory=dict)
    history: List[Dict] = field(default_factory=list)
    verify_output: str = ""


class RepairLemmaRunner:
    """修复引理构造 + 引理修正机制的回路编排（论文 2.3.3、4.1.4）。"""

    def __init__(
        self,
        config,
        *,
        load_prompt_template: Callable[[str], Tuple[str, str]],
        call_stage_llm: Callable[[str, str, str], str],
    ) -> None:
        self.config = config
        self._load_prompt_template = load_prompt_template
        self._call_stage_llm = call_stage_llm

    # ---------- 提示词组装 ----------
    def build_repair_blocks(self, ctx: RepairLemmaContext, marked_proof: str) -> List[str]:
        from .construct_lemma_generator import (
            format_function_definitions_block,
            format_theorem_statement_block,
        )

        return [
            format_function_definitions_block(ctx.theorem_data),
            format_theorem_statement_block(ctx.theorem_data),
            marked_proof,
            format_isabelle_error_for_prompt(ctx.verify_output),
        ]

    def build_revision_blocks(
        self,
        ctx: RepairLemmaContext,
        marked_proof: str,
        previous_lemma: Dict[str, str],
    ) -> List[str]:
        blocks = self.build_repair_blocks(ctx, marked_proof)
        blocks.append(format_previous_lemma_block(previous_lemma))
        return blocks

    # ---------- 单轮调用 ----------
    def construct_repair_lemmas(
        self, ctx: RepairLemmaContext, marked_proof: str
    ) -> List[Dict[str, str]]:
        sys_p, user_t = self._load_prompt_template(ctx.repair_prompt_path)
        user = _fill_user_provide(user_t, self.build_repair_blocks(ctx, marked_proof))
        raw = self._call_stage_llm("repair_lemma_construct", sys_p, user)
        return parse_lemmas_with_thoughts(raw)

    def revise_lemma(
        self,
        ctx: RepairLemmaContext,
        marked_proof: str,
        previous_lemma: Dict[str, str],
    ) -> List[Dict[str, str]]:
        sys_p, user_t = self._load_prompt_template(ctx.revision_prompt_path)
        user = _fill_user_provide(
            user_t, self.build_revision_blocks(ctx, marked_proof, previous_lemma)
        )
        raw = self._call_stage_llm("repair_lemma_revise", sys_p, user)
        return parse_lemmas_with_thoughts(raw)

    # ---------- 回路 ----------
    def run_loop(
        self,
        ctx: RepairLemmaContext,
        *,
        verify_callback: Callable[[], Tuple[bool, str]],
    ) -> RepairLemmaResult:
        """
        构造修复引理 -> 并入 unproven 引理库 -> 重新验证 sketch；
        仍失败则带上"先前失败的引理"进入引理修正机制（图 2-11/2-12），最多 max_attempts 轮。

        断裂点标记只出现在发给模型的提示词里，不写回工作 .thy（避免污染后续阶段），
        带标记的版本作为产物单独落盘。
        """
        result = RepairLemmaResult(verify_output=ctx.verify_output)
        thy_text = Path(ctx.theory_file).read_text(encoding="utf-8")
        marker_line = pick_break_line(thy_text, ctx.verify_output)
        if marker_line is None:
            logger.warning("修复引理构造：未能从报错定位断裂点，跳过")
            return result
        result.marker_line = marker_line
        marked_full = inject_break_marker(thy_text, marker_line)
        marked_proof = extract_theory_body(marked_full) or marked_full

        previous: Optional[Dict[str, str]] = None
        seen_payloads: set = set()
        max_attempts = max(1, int(ctx.max_attempts))
        for attempt in range(1, max_attempts + 1):
            result.attempts = attempt
            if previous is None:
                lemmas = self.construct_repair_lemmas(ctx, marked_proof)
                stage = "repair_lemma_construct"
            else:
                lemmas = self.revise_lemma(ctx, marked_proof, previous)
                stage = "repair_lemma_revise"
            if not lemmas:
                result.history.append(
                    {"attempt": attempt, "stage": stage, "error": "no_lemma_parsed"}
                )
                break

            payload = "\n\n".join(lemma["statement"] for lemma in lemmas)
            if payload in seen_payloads:
                # 引理修正机制给出的引理与上一轮完全相同 -> 无进展，提前结束
                result.history.append(
                    {
                        "attempt": attempt,
                        "stage": stage,
                        "error": "no_progress_same_lemmas",
                    }
                )
                break
            seen_payloads.add(payload)
            merged = UnprovenLemmaStore.merge_extra_lemmas_into_unproven_thy(
                ctx.unproven_thy_path,
                payload,
                ctx.unproven_thy_path.stem,
                packages=ctx.theorem_data.get("packages", "Main") or "Main",
                theorem_data=ctx.theorem_data,
                domain=ctx.theorem_data.get("domain", "") or "",
            )
            result.lemmas = lemmas
            result.merged_names += [n for n in merged if n not in result.merged_names]
            for _lem in lemmas:
                _lname = _lem.get("name")
                _llabel = (_lem.get("linear_label") or "").strip()
                if _lname and _llabel:
                    result.linear_labels[_lname] = _llabel
            _write_text(
                ctx.result_dir / f"repair_lemma_{attempt}_marked.thy", marked_full
            )
            _write_json(
                ctx.result_dir / f"repair_lemma_{attempt}.json",
                {
                    "attempt": attempt,
                    "stage": stage,
                    "marker_line": marker_line,
                    "lemmas": lemmas,
                    "merged_names": merged,
                },
            )

            success, verify_output = verify_callback()
            if verify_output:
                result.verify_output = verify_output
            result.history.append(
                {
                    "attempt": attempt,
                    "stage": stage,
                    "merged_names": merged,
                    "verify_success": bool(success),
                }
            )
            if success:
                result.success = True
                result.merged_names = list(merged)
                _write_json(ctx.result_dir / "repair_lemma_loop.json", result.history)
                return result

            previous = lemmas[-1]
            next_text = Path(ctx.theory_file).read_text(encoding="utf-8")
            next_line = pick_break_line(next_text, result.verify_output)
            if next_line is not None:
                marker_line = next_line
                marked_full = inject_break_marker(next_text, next_line)
                marked_proof = extract_theory_body(marked_full) or marked_full
        _write_json(ctx.result_dir / "repair_lemma_loop.json", result.history)
        return result


def _write_json(path: Path, payload) -> None:
    try:
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        Path(path).write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except Exception as exc:  # pragma: no cover - 落盘失败不影响主流程
        logger.warning("写入 %s 失败: %s", path, exc)


def _write_text(path: Path, text: str) -> None:
    try:
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        Path(path).write_text(text or "", encoding="utf-8")
    except Exception as exc:  # pragma: no cover
        logger.warning("写入 %s 失败: %s", path, exc)
