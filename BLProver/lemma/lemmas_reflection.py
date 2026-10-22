"""
引理反思：验证 unproven_lemmas.thy 中 sorry 引理的陈述是否通过 Isabelle 类型检查；
失败时将错误反馈 LLM 并重写引理陈述。

提示词：BLProver/prompt/lemmas_reflection_prompt.txt
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence

from ..config import BLProverConfig
from ..sketch.construct_lemma_generator import (
    _USER_PROVIDE,
    format_function_definitions_block,
    format_theorem_statement_block,
    split_construct_lemma_prompt_file,
)
from ..utils.isabelle_sledgehammer import (
    IsabelleRunnerConfig,
    IsabelleServerSessionPool,
    _mark_thy_disk_changed,
    format_isabelle_error_for_prompt,
    verify_thy_with_repair,
)
from ..utils.lemma_dedup import extract_fact_name
from .unproven_lemma_store import (
    UnprovenLemmaStore,
    quote_composite_fixes_types,
    strip_lemma_proof_body,
)

logger = logging.getLogger(__name__)

LEMMAS_REFLECTION_PROMPT_FILENAME = "lemmas_reflection_prompt.txt"
LEMMAS_REFLECTION_USER_PLACEHOLDERS = 5

_JSON_FENCE_RE = re.compile(
    r"```(?:json)?\s*(\{.*?\})\s*```",
    re.DOTALL | re.IGNORECASE,
)

_STATEMENT_ERROR_MARKERS = (
    "Type unification failed",
    "Type error in application",
    "Bad context for command",
    "Undefined fact",
    "Inner syntax error",
    "Outer syntax error",
    "Failed to parse prop",
    "Illegal type parameters",
    "Malformed command",
    "ok=False",
)


def default_lemmas_reflection_prompt_path(pkg_root: Path) -> Path:
    return pkg_root / "prompt" / LEMMAS_REFLECTION_PROMPT_FILENAME


def fill_lemmas_reflection_user_template(
    user_template: str,
    func_block: str,
    theorem_block: str,
    unproven_thy_text: str,
    isabelle_error: str,
    informal_proof: str,
    prompt_path: str,
) -> str:
    replacements = [
        (func_block or "").strip(),
        (theorem_block or "").strip(),
        (unproven_thy_text or "").strip(),
        (isabelle_error or "").strip(),
        (informal_proof or "").strip(),
    ]
    count = user_template.count(_USER_PROVIDE)
    if count != LEMMAS_REFLECTION_USER_PLACEHOLDERS:
        raise ValueError(
            f"引理反思提示词占位符 {_USER_PROVIDE!r} 数量应为 "
            f"{LEMMAS_REFLECTION_USER_PLACEHOLDERS}，实际为 {count}: {prompt_path}"
        )
    out = user_template
    for block in replacements:
        out = out.replace(_USER_PROVIDE, block, 1)
    return out


_VALID_JSON_ESCAPE_LEAD = frozenset('"\\/bfnrtu')


def _sanitize_json_invalid_backslashes(text: str) -> str:
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


def _loads_reflection_json(text: str) -> Dict[str, Any]:
    last_exc: Optional[json.JSONDecodeError] = None
    for candidate in (text, _sanitize_json_invalid_backslashes(text)):
        try:
            data = json.loads(candidate)
            if isinstance(data, dict):
                return data
            raise ValueError("引理反思 JSON 根节点必须是 object")
        except json.JSONDecodeError as exc:
            last_exc = exc
    assert last_exc is not None
    raise last_exc


def parse_lemmas_reflection_json(raw: str) -> Dict[str, Any]:
    text = (raw or "").strip()
    if not text:
        raise ValueError("引理反思 LLM 返回为空")

    fence = _JSON_FENCE_RE.search(text)
    if fence:
        text = fence.group(1).strip()
    else:
        start = text.find("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            text = text[start : end + 1]

    data = _loads_reflection_json(text)
    stmts = data.get("lemma_statements")
    if not isinstance(stmts, list) or not stmts:
        raise ValueError("引理反思 JSON 缺少非空 lemma_statements 数组")
    cleaned: List[str] = []
    for item in stmts:
        if not isinstance(item, str) or not item.strip():
            raise ValueError("lemma_statements 每项必须为非空字符串")
        cleaned.append(normalize_lemma_statement(item))
    data["lemma_statements"] = cleaned
    return data


def normalize_lemma_statement(statement: str) -> str:
    text = _sanitize_isabelle_tokens_in_text((statement or "").strip())
    if not text:
        return text
    text = strip_lemma_proof_body(text)
    text = quote_composite_fixes_types(text)
    if not re.search(r"\bsorry\b", text, re.IGNORECASE):
        text = text.rstrip() + "\n  sorry"
    return text


def _sanitize_isabelle_tokens_in_text(text: str) -> str:
    """LLM JSON 偶发把 \\<not> 等写成 \\u0008not（退格符）。"""
    if not text:
        return text
    text = text.replace("\u0008", "\\<")
    return text


def unproven_lemma_statements_valid(verify_result: dict) -> bool:
    if not verify_result.get("success"):
        return False
    out = verify_result.get("verify_output") or ""
    return not any(marker in out for marker in _STATEMENT_ERROR_MARKERS)


def verify_unproven_lemmas_thy(
    unproven_thy_path: Path,
    isabelle_config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> dict:
    """仅验证 unproven_lemmas.thy（sorry 占位），不做 sledgehammer / 证明步 repair。"""
    cfg = IsabelleRunnerConfig(
        isabelle_path=isabelle_config.isabelle_path,
        isabelle_home=isabelle_config.isabelle_home,
        timeout=isabelle_config.timeout,
        verify_timeout=isabelle_config.verify_timeout,
        verify_wall_timeout_sec=isabelle_config.verify_wall_timeout_sec,
        use_theories_heartbeat_sec=isabelle_config.use_theories_heartbeat_sec,
        max_sledgehammer_rounds=isabelle_config.max_sledgehammer_rounds,
        max_failure_repair_rounds=isabelle_config.max_failure_repair_rounds,
        repair_failed_steps=False,
        use_server=isabelle_config.use_server,
        kill_orphan_poly_on_shutdown=isabelle_config.kill_orphan_poly_on_shutdown,
    )
    result = verify_thy_with_repair(
        str(unproven_thy_path),
        cfg,
        server_pool=server_pool,
    )
    result["success"] = unproven_lemma_statements_valid(result)
    return result


@dataclass
class LemmasReflectionAttempt:
    attempt: int
    success: bool
    verify_output: str = ""
    explanation: str = ""
    llm_raw: str = ""


@dataclass
class LemmasReflectionResult:
    success: bool = False
    lemma_statements: List[str] = field(default_factory=list)
    attempts: int = 0
    verify_output: str = ""
    attempts_log: List[LemmasReflectionAttempt] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "success": self.success,
            "attempts": self.attempts,
            "lemma_count": len(self.lemma_statements),
            "verify_output": self.verify_output,
            "attempts_log": [
                {
                    "attempt": a.attempt,
                    "success": a.success,
                    "explanation": a.explanation,
                }
                for a in self.attempts_log
            ],
        }


class LemmasReflectionRunner:
    """验证并重写 unproven 引理陈述（sorry 占位）。"""

    def __init__(
        self,
        config: BLProverConfig,
        *,
        load_prompt_template: Callable[[str], tuple[str, str]],
        call_stage_llm: Callable[[str, str, str], str],
    ):
        self.config = config
        self._load_prompt_template = load_prompt_template
        self._call_stage_llm = call_stage_llm
        prompt_path = config.lemmas_reflection_prompt_path or str(
            default_lemmas_reflection_prompt_path(
                Path(__file__).resolve().parent.parent.parent
            )
        )
        self._prompt_path = prompt_path

    def reflect_until_valid(
        self,
        *,
        unproven_thy_path: Path,
        lemma_statements: Sequence[str],
        theorem_data: dict,
        informal_proof: str,
        domain: str,
        packages: str,
        unproven_thy_name: str,
        isabelle_config: IsabelleRunnerConfig,
        server_pool: Optional[IsabelleServerSessionPool] = None,
    ) -> LemmasReflectionResult:
        max_attempts = max(1, self.config.max_lemmas_reflection_attempts)
        current = [normalize_lemma_statement(s) for s in lemma_statements if (s or "").strip()]
        if not current:
            return LemmasReflectionResult(success=True, lemma_statements=[])

        result = LemmasReflectionResult(lemma_statements=list(current))
        own_pool: Optional[IsabelleServerSessionPool] = None
        pool = server_pool
        if pool is None or not pool.is_active:
            own_pool = IsabelleServerSessionPool(isabelle_config)
            own_pool.__enter__()
            pool = own_pool

        try:
            for attempt in range(1, max_attempts + 1):
                UnprovenLemmaStore.write_unproven_lemma_thy(
                    unproven_thy_path,
                    current,
                    unproven_thy_name,
                    packages=packages,
                    domain=domain,
                )
                _mark_thy_disk_changed(pool)
                if pool is not None and pool.is_active:
                    # Every round rewrites the .thy file, so drop the stale
                    # session snapshot first (purge without restart; if purge
                    # fails refresh_session_if_stale restarts the session).
                    pool.refresh_session_if_stale(unproven_thy_path)
                print(
                    f"\n[lemmas-reflection {attempt}/{max_attempts}] "
                    f"验证 {unproven_thy_path.name}（引理陈述 + sorry）...",
                    flush=True,
                )
                verify_result = verify_unproven_lemmas_thy(
                    unproven_thy_path,
                    isabelle_config,
                    server_pool=pool,
                )
                verify_out = verify_result.get("verify_output") or ""
                ok = bool(verify_result.get("success"))
                log_entry = LemmasReflectionAttempt(
                    attempt=attempt,
                    success=ok,
                    verify_output=verify_out,
                )
                result.attempts_log.append(log_entry)
                result.attempts = attempt
                result.verify_output = verify_out

                if ok:
                    result.success = True
                    result.lemma_statements = list(current)
                    print(
                        f"[lemmas-reflection {attempt}/{max_attempts}] "
                        f"引理陈述验证通过（{len(current)} 条）",
                        flush=True,
                    )
                    return result

                if attempt >= max_attempts:
                    break

                error_for_prompt = format_isabelle_error_for_prompt(
                    verify_out, max_chars=8000
                )
                func_block = format_function_definitions_block(theorem_data)
                theorem_block = format_theorem_statement_block(theorem_data)
                unproven_text = unproven_thy_path.read_text(encoding="utf-8")
                sys_prompt, user_tpl = self._load_prompt_template(self._prompt_path)
                user_prompt = fill_lemmas_reflection_user_template(
                    user_tpl,
                    func_block,
                    theorem_block,
                    unproven_text,
                    error_for_prompt,
                    informal_proof or "",
                    self._prompt_path,
                )
                print(
                    f"[lemmas-reflection {attempt}/{max_attempts}] "
                    f"验证未通过，请求 LLM 修正引理陈述 ...",
                    flush=True,
                )
                raw = self._call_stage_llm(
                    f"lemmas_reflection_{attempt}",
                    sys_prompt,
                    user_prompt,
                )
                log_entry.llm_raw = raw
                try:
                    parsed = parse_lemmas_reflection_json(raw)
                except ValueError as exc:
                    logger.warning("引理反思 JSON 解析失败: %s", exc)
                    log_entry.explanation = f"JSON 解析失败: {exc}"
                    continue

                new_stmts = parsed.get("lemma_statements") or []
                explanation = str(parsed.get("explanation") or "").strip()
                log_entry.explanation = explanation
                if explanation:
                    logger.info("引理反思说明: %s", explanation[:500])

                if len(new_stmts) != len(current):
                    logger.warning(
                        "引理反思返回数量 %d 与原 %d 不一致，按名称尽量对齐",
                        len(new_stmts),
                        len(current),
                    )
                current = _merge_reflected_statements(current, new_stmts)
                result.lemma_statements = list(current)

            result.success = False
            print(
                f"[lemmas-reflection] {max_attempts} 轮后仍未通过引理陈述验证",
                flush=True,
            )
            return result
        finally:
            if own_pool is not None:
                own_pool.__exit__(None, None, None)


def _merge_reflected_statements(
    previous: Sequence[str],
    reflected: Sequence[str],
) -> List[str]:
    """优先按引理名对齐；数量一致时直接采用 reflected。"""
    if len(reflected) == len(previous):
        return [normalize_lemma_statement(s) for s in reflected]

    by_name: Dict[str, str] = {}
    for stmt in reflected:
        name = extract_fact_name(stmt)
        if name:
            by_name[name] = normalize_lemma_statement(stmt)

    merged: List[str] = []
    for old in previous:
        name = extract_fact_name(old)
        if name and name in by_name:
            merged.append(by_name.pop(name))
        else:
            merged.append(normalize_lemma_statement(old))
    for stmt in by_name.values():
        merged.append(stmt)
    return merged


def prune_invalid_lemma_statements(
    statements: Sequence[str],
    *,
    unproven_thy_path: Path,
    unproven_thy_name: str,
    packages: str,
    domain: str,
    isabelle_config: IsabelleRunnerConfig,
    server_pool: Optional[IsabelleServerSessionPool] = None,
    max_rounds: int = 20,
) -> List[str]:
    """
    引理反思仍失败时，按 Isabelle 报错行定位并移除类型/语法非法的引理块。
    """
    from ..lemma_proving.iterator import _lemma_line_span_1based
    from ..lemma_proving.usage import lemma_blocks_in_thy
    from ..utils.isabelle_sledgehammer import iter_isabelle_server_error_messages

    current = [normalize_lemma_statement(s) for s in statements if (s or "").strip()]
    if not current:
        return []

    for round_idx in range(1, max_rounds + 1):
        UnprovenLemmaStore.write_unproven_lemma_thy(
            unproven_thy_path,
            current,
            unproven_thy_name,
            packages=packages,
            domain=domain,
        )
        verify_result = verify_unproven_lemmas_thy(
            unproven_thy_path,
            isabelle_config,
            server_pool=server_pool,
        )
        if verify_result.get("success"):
            if round_idx > 1:
                print(
                    f"[lemmas-reflection] 剪枝后引理陈述验证通过（{len(current)} 条）",
                    flush=True,
                )
            return current

        verify_out = verify_result.get("verify_output") or ""
        unproven_text = unproven_thy_path.read_text(encoding="utf-8")
        bad_names: set[str] = set()
        for _msg, line_no, _fpath in iter_isabelle_server_error_messages(
            verify_out, file_filter=str(unproven_thy_path)
        ):
            for name in lemma_blocks_in_thy(unproven_text):
                span = _lemma_line_span_1based(unproven_text, name)
                if span and span[0] <= line_no <= span[1]:
                    bad_names.add(name)
                    break

        if not bad_names:
            logger.warning("引理剪枝：无法从报错定位无效引理，停止剪枝")
            break

        before = len(current)
        current = [
            s
            for s in current
            if extract_fact_name(s) not in bad_names
        ]
        print(
            f"[lemmas-reflection] 剪枝轮 {round_idx}: 移除无效引理 "
            f"{sorted(bad_names)}（{before} → {len(current)} 条）",
            flush=True,
        )
        if len(current) == before:
            break

    return current
