"""
根据 prompt/construct lemma prompt.txt 调用 LLM，得到非形式化证明与 new lemma 列表。
"""

from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from ..llm.base import LLMInterface
from ..utils.isabelle_parser import IsabelleParser

logger = logging.getLogger(__name__)

_TASK_SPLIT_PATTERN = re.compile(
    r"####\s*below\s+are\s+(?:your\s+task|user\s+inputs)",
    re.IGNORECASE,
)
_USER_PROVIDE = "{{user provide}}"


@dataclass
class ConstructLemmaResult:
    informal_proof: str = ""
    lemma_statements: List[str] = field(default_factory=list)
    """解析出的 Isabelle 引理全文（含 lemma 行）。"""
    raw_response: str = ""
    lemma_concepts: List[Dict[str, str]] = field(default_factory=list)
    """供 SketchGenerator 使用：name + description（Isabelle 陈述）+ meaning/source。"""


def ordered_function_definition_items(
    fdefs: Dict[str, str],
    function_names: Optional[List[str]] = None,
) -> List[Tuple[str, str]]:
    """
    按 function names 顺序返回 (名称, 定义文本) 列表；
    未列出的定义按名称排序追加（与 prompt / .thy 组装一致）。
    """
    if not isinstance(fdefs, dict):
        return []
    seen: set[str] = set()
    items: List[Tuple[str, str]] = []
    if isinstance(function_names, list):
        for name in function_names:
            if name in fdefs and name not in seen:
                items.append((name, str(fdefs[name]).strip()))
                seen.add(name)
    for key in sorted(fdefs.keys()):
        if key not in seen:
            items.append((key, str(fdefs[key]).strip()))
            seen.add(key)
    # definition 可能引用 fun/primrec，须排在后面（与 defs.thy 组装一致）
    primaries = [(n, d) for n, d in items if not d.lstrip().startswith("definition ")]
    definitions = [(n, d) for n, d in items if d.lstrip().startswith("definition ")]
    return primaries + definitions


def format_function_definitions_block(theorem_data: Dict) -> str:
    """与理论文件一致的函数定义文本顺序（含同领域补充定义）。"""
    parts: List[str] = []
    other = (theorem_data.get("other formal") or "").strip()
    if other:
        parts.append(other)

    fdefs = theorem_data.get("formal function definitions") or {}
    for _name, defn in ordered_function_definition_items(
        fdefs, theorem_data.get("function names")
    ):
        if defn:
            parts.append(defn)

    block = "\n\n".join(p for p in parts if p)

    # 领域级补充定义：与 defs.thy 同源，避免提示词缺少跨数据文件的依赖定义
    domain_block = (theorem_data.get("domain definitions") or "").strip()
    if domain_block:
        from ..lemma.proven_lemma_store import ProvenLemmaStore

        block = ProvenLemmaStore.merge_definition_preambles(block, domain_block)

    return block


def format_theorem_statement_block(theorem_data: Dict) -> str:
    stmt = (theorem_data.get("formal theorem statement") or "").strip()
    return f"```isabelle\n{stmt}\n```"


def split_construct_lemma_prompt_file(text: str) -> Tuple[str, str]:
    m = _TASK_SPLIT_PATTERN.search(text)
    if not m:
        raise ValueError(
            "提示词中未找到分隔标记 '####below are your task' 或 "
            "'####below are user inputs'，请检查 prompt 文件。"
        )
    system_prompt = text[: m.start()].strip()
    user_template = text[m.start() :].strip()
    return system_prompt, user_template


def fill_user_prompt(user_template: str, func_block: str, theorem_block: str) -> str:
    out = user_template
    for repl in (func_block, theorem_block):
        if _USER_PROVIDE not in out:
            raise ValueError("user 模板中 {{user provide}} 占位符数量不足 2 个")
        out = out.replace(_USER_PROVIDE, repl, 1)
    return out


def _strip_informal_braces(text: str) -> str:
    s = text.strip()
    s = re.sub(r"^\s*\{\{", "", s)
    s = re.sub(r"\}\}\s*$", "", s)
    return s.strip()


def sanitize_informal_proof_text(text: str) -> str:
    """
    去掉误并入 informal 的引理段（避免草图 user 里 ### Informal proof 与
    ###potentially useful lemmas 重复同一段 lemma）。
    """
    if not (text or "").strip():
        return (text or "").strip()
    s = text.strip()
    for pat in (
        r"(?is)##\s*Required\s+new\s+lemma\b",
        r"(?is)###\s*new\s+lemma\s*\d+\b",
    ):
        m = re.search(pat, s)
        if m:
            s = s[: m.start()].rstrip()
    return s


def _extract_informal_proof(response: str) -> str:
    """多种标题/结束边界，尽量提取非形式化证明（不使用吞到全文末尾的 \\Z 模式）。"""
    end_after_required = r"(?=##\s*Required\s+new\s+lemma)"
    end_before_new_lemma = r"(?=###\s*new\s+lemma\s*\d+)"
    end_before_required_hash = r"(?=##\s*Required)"
    hdr = r"(?is)#{2,3}\s*Informal\s+proof\s*"
    patterns = [
        hdr + r"(.*?)" + end_after_required,
        hdr + r"(.*?)" + end_before_new_lemma,
        hdr + r"(.*?)" + end_before_required_hash,
    ]
    for pat in patterns:
        inf_m = re.search(pat, response, re.DOTALL)
        if inf_m:
            t = _strip_informal_braces(inf_m.group(1))
            if t:
                return sanitize_informal_proof_text(t)
    # 弱兜底：勿用「任意 ^## 行」作边界（正文里常有 ## Step1）；仅认节标题
    weak = re.search(
        r"(?is)\bInformal\s+proof\s*:?\s*\n(.+?)(?=^(?:##\s*Required\s+new\s+lemma|###\s*new\s+lemma\s*\d+)\b|\Z)",
        response,
        re.MULTILINE | re.DOTALL,
    )
    if weak:
        t = _strip_informal_braces(weak.group(1))
        if t and len(t) < 50000:
            return sanitize_informal_proof_text(t)
    # 模型把证明包在 {{ ... }} 里且紧跟 ## Required new lemma（无 ### Informal proof 标题）
    brace = re.search(
        r"(?is)\{\{\s*(.+?)\s*\}\}\s*(?=\n\s*##\s*Required\s+new\s+lemma\b)",
        response,
        re.DOTALL,
    )
    if brace:
        t = _strip_informal_braces(brace.group(1))
        if t:
            return sanitize_informal_proof_text(t)
    return ""


def extract_informal_proof_fallback_from_raw(raw: str) -> str:
    """
    主解析仍为空时，从构造阶段全文再试（避免重复调用 _extract_informal_proof）；
    仅截到 Required / ### new lemma，且不用「任意 ## 行」作边界。
    """
    if not (raw or "").strip():
        return ""
    for pat in (
        r"(?is)^#+\s*Informal\s+proof\s*\n(.+?)(?=^(?:##\s*Required\s+new\s+lemma|###\s*new\s+lemma\s*\d+)\b|\Z)",
        r"(?is)\bInformal\s+proof\s*:?\s*\n(.+?)(?=^(?:##\s*Required\s+new\s+lemma|###\s*new\s+lemma\s*\d+)\b|\Z)",
    ):
        m = re.search(pat, raw, re.MULTILINE | re.DOTALL)
        if m:
            t = sanitize_informal_proof_text(_strip_informal_braces(m.group(1)))
            if t.strip():
                return t
    bm = re.search(
        r"(?is)\{\{\s*(.+?)\s*\}\}\s*(?=\n\s*##\s*Required\s+new\s+lemma\b)",
        raw,
        re.DOTALL,
    )
    if bm:
        t = sanitize_informal_proof_text(_strip_informal_braces(bm.group(1)))
        if t.strip():
            return t
    return ""


def parse_construct_lemma_response(response: str) -> Tuple[str, List[Dict[str, str]]]:
    """
    从 LLM 输出中提取非形式化证明与引理列表。
    每项含 statement（Isabelle 全文）与 meaning/source（可为空）。
    """
    informal = _extract_informal_proof(response)
    informal = sanitize_informal_proof_text(informal)

    req = re.search(
        r"##\s*Required\s+new\s+lemma\s*(.*)\Z",
        response,
        re.DOTALL | re.IGNORECASE,
    )
    lemma_section = (req.group(1) if req else "").strip()
    if not lemma_section:
        lemma_section = response

    _fence = "```"
    lemma_block_pat = (
        r"###\s*new\s+lemma\s*(\d+)\s*(.*?)"
        + _fence
        + r"\s*isabelle\s*(.*?)"
        + _fence
    )

    raw_entries: List[Dict[str, str]] = []
    last_end = 0
    for m in re.finditer(lemma_block_pat, lemma_section, re.DOTALL | re.IGNORECASE):
        body = m.group(3).strip()
        if not body:
            last_end = m.end()
            continue
        pre = lemma_section[last_end : m.start()]
        # Meaning/Source/Linear label 由模型写在 `### new lemmaN` 之后、```isabelle 之前，
        # 即落在本次匹配的 m.group(2) 内；pre 仅作非法排版的兜底。
        header = (m.group(2) or "") + "\n" + pre
        meaning = ""
        source = ""
        linear_label = ""
        m_mean = re.search(
            r"(?is)meaning\s*:\s*(.*?)(?=\n\s*(?:source\s*:|linear\s*label\s*:|###\s*new\s+lemma\s*\d+)|\Z)",
            header,
        )
        if m_mean:
            meaning = m_mean.group(1).strip()
        m_src = re.search(
            r"(?is)source\s*:\s*(.*?)(?=\n\s*(?:linear\s*label\s*:|###\s*new\s+lemma\s*\d+)|\Z)",
            header,
        )
        if m_src:
            source = m_src.group(1).strip()
        m_lin = re.search(
            r"(?is)linear\s*label\s*:?\s*(.*?)(?=\n\s*###\s*new\s+lemma\s*\d+|\Z)",
            header,
        )
        if m_lin:
            linear_label = m_lin.group(1).strip()
        raw_entries.append(
            {
                "statement": body,
                "meaning": meaning,
                "source": source,
                "linear_label": linear_label,
            }
        )
        last_end = m.end()

    if not raw_entries and lemma_section:
        fallback_pat = _fence + r"\s*isabelle\s*(.*?)" + _fence
        for m in re.finditer(fallback_pat, lemma_section, re.DOTALL | re.IGNORECASE):
            body = m.group(1).strip()
            if body:
                raw_entries.append(
                    {
                        "statement": body,
                        "meaning": "",
                        "source": "",
                        "linear_label": "",
                    }
                )

    parser = IsabelleParser()
    seen = set()
    unique: List[Dict[str, str]] = []
    for item in raw_entries:
        key = parser.normalize_statement(item["statement"])
        if key in seen:
            continue
        seen.add(key)
        unique.append(
            {
                "statement": item["statement"],
                "meaning": item.get("meaning") or "",
                "source": item.get("source") or "",
                "linear_label": item.get("linear_label") or "",
            }
        )

    return informal, unique


class ConstructLemmaGenerator:
    def __init__(self, llm: LLMInterface, prompt_path: str):
        self.llm = llm
        self.prompt_path = Path(prompt_path)
        raw = self.prompt_path.read_text(encoding="utf-8")
        self._system_prompt, self._user_template = split_construct_lemma_prompt_file(raw)

    def generate(self, theorem_data: Dict) -> ConstructLemmaResult:
        theorem_name = theorem_data.get("theorem name", "theorem")
        func_block = format_function_definitions_block(theorem_data)
        th_block = format_theorem_statement_block(theorem_data)
        user_prompt = fill_user_prompt(self._user_template, func_block, th_block)

        raw = self.llm.generate(user_prompt, self._system_prompt)
        informal, parsed_lemmas = parse_construct_lemma_response(raw)
        if not (informal or "").strip() and (raw or "").strip():
            fb = extract_informal_proof_fallback_from_raw(raw)
            if fb.strip():
                informal = fb
                logger.info("构造引理：主解析 informal 为空，已用 raw 二次提取非形式化证明")

        stmts = [x["statement"] for x in parsed_lemmas]
        concepts: List[Dict[str, str]] = []
        for i, item in enumerate(parsed_lemmas, start=1):
            concepts.append(
                {
                    "name": f"constructed_lemma_{i}",
                    "description": item["statement"],
                    "meaning": item.get("meaning") or "",
                    "source": item.get("source") or "",
                    "linear_label": item.get("linear_label") or "",
                }
            )

        if not informal and not stmts:
            logger.warning(
                "构造引理 LLM 返回未能解析出 informal / new lemma（theorem=%s）",
                theorem_name,
            )

        return ConstructLemmaResult(
            informal_proof=informal,
            lemma_statements=stmts,
            raw_response=raw,
            lemma_concepts=concepts,
        )
