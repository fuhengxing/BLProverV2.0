"""
构造引理去重与 .thy 草图合并：避免 Duplicate fact / Bad context。
"""

from __future__ import annotations

import logging
import re
from typing import List, Optional, Set, Tuple

logger = logging.getLogger(__name__)

_FACT_HEAD_RE = re.compile(
    r"^\s*(lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE | re.MULTILINE,
)
_PROP_IN_QUOTES_RE = re.compile(r'"([^"]*)"')
_SHOWS_RE = re.compile(r"(?is)shows\s+\"([^\"]*)\"")
_ASSUMES_SHOWS_BLOCK_RE = re.compile(
    r"(?is)(?:fixes\s+.*)?(?:assumes\s+.*?)?shows\s+\"([^\"]*)\""
)

_FACT_REF_RE = re.compile(
    r"(?:using|unfolding|intro|elim|rule|simp|intro|dest|method|erule|drule|frule)\s+"
    r"([A-Za-z0-9_']+)"
    r"(?:\s|,|\[|\)|$|:)",
    re.IGNORECASE | re.MULTILINE,
)
_BY_FACT_RE = re.compile(
    r"\bby\s+\(?([A-Za-z0-9_']+)",
    re.IGNORECASE,
)
_SIMP_ADD_RE = re.compile(
    r"\b(?:simp\s+add|unfolding)\s*:\s*([A-Za-z0-9_',\s]+)",
    re.IGNORECASE,
)
# 匹配 by/apply (method arg1 arg2 ...) 中的引理名：提取括号内全部非修饰词标识符
_BY_PAREN_ARGS_RE = re.compile(
    r"\b(?:by|apply)\s*\(([^)]+)\)",
    re.IGNORECASE,
)
# method 参数中的修饰前缀（add: / del: / split: / flip: 等），后面跟的才是引理名
_BY_MODIFIER_RE = re.compile(
    r"\b(?:add|del|simp|split|flip|iff|dest|elim|intro|rule|of|OF|THEN|symmetric|rotated|where|for|arbitrary|changed|folded|unfolded)\s*:",
    re.IGNORECASE,
)

# collect_fact_names_from_sketch / proof 引用分析时过滤 Isabelle 关键字与局部 have 名
_SKIP_PROOF_REF_NAMES = frozenset(
    {
        "auto",
        "simp",
        "blast",
        "fastforce",
        "force",
        "eval",
        "arith",
        "linarith",
        "clarsimp",
        "metis",
        "presburger",
        "smt",
        "intro",
        "elim",
        "rule",
        "drule",
        "erule",
        "frule",
        "subst",
        "proof",
        "done",
        "sorry",
        "unfolding",
        "using",
        "have",
        "show",
        "then",
        "from",
        "with",
        "cases",
        "case",
        "induction",
        "add",
        "of",
        "THEN",
        "where",
        "for",
    }
)


def _normalize_prop_text(prop: str) -> str:
    s = (prop or "").strip()
    s = re.sub(r"\s+", " ", s)
    for old in (
        "⟷",
        "↔",
        "<->",
        "\\<longleftrightarrow>",
        "\\<Leftrightarrow>",
        "\\<equiv>",
    ):
        s = s.replace(old, "<->")
    return re.sub(r"\s+", " ", s).strip()


_ISABELLE_PROP_CONSTANTS = frozenset(
    {
        "True",
        "False",
        "None",
        "Some",
        "Suc",
        "Nil",
        "Cons",
        "Pair",
        "length",
        "fst",
        "snd",
        "hd",
        "tl",
        "map",
        "set",
        "List",
        "option",
        "nat",
        "int",
        "bool",
        "prod",
        "if",
        "let",
        "in",
        "and",
        "or",
        "not",
        "All",
        "Ex",
        "push",
        "pop",
        "top",
        "size",
        "capacity",
        "isfull",
        "isempty",
        "empty",
        "full",
        "alist",
        "Abs_bstack",
        "bstack",
    }
)


def alpha_normalize_proposition_key(prop: str) -> str:
    """
    将命题中的短绑定变量名规范化为 _b0/_b1/...，便于识别 v/x 等等价引理。
    """
    s = _normalize_prop_text(prop)
    mapping: dict[str, str] = {}
    counter = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal counter
        word = match.group(0)
        if word in _ISABELLE_PROP_CONSTANTS:
            return word
        if len(word) <= 3 and word.islower():
            if word not in mapping:
                mapping[word] = f"_b{counter}"
                counter += 1
            return mapping[word]
        return word

    return re.sub(r"[a-z][a-z0-9_']*", repl, s)


_FULL_STATEMENT_RE = re.compile(
    r'(?is)(fixes\s+.*?shows\s+"[^"]*")',
)
_FULL_STATEMENT_ASSUMES_RE = re.compile(
    r'(?is)(assumes\s+.*?shows\s+"[^"]*")',
)


def extract_full_statement_text(block: str) -> str:
    """
    提取引理完整陈述文本（fixes/assumes/shows 上下文），用于 alpha 规范化。

    关键：alpha 规范化必须基于完整陈述，而非仅 shows 子句。否则像
        assumes "t = Node l x r" shows "complete l"
        assumes "t = Node l x r" shows "complete r"
    仅看 shows 时 l 与 r 都被映射成首个绑定变量而误判等价；但 l/r 在
    假设中分别扮演左/右子树角色，不可互换，二者并非 alpha 等价。
    """
    text = (block or "").strip()
    if not text:
        return ""
    m = _FULL_STATEMENT_RE.search(text)
    if m:
        return _normalize_prop_text(m.group(1))
    m = _FULL_STATEMENT_ASSUMES_RE.search(text)
    if m:
        return _normalize_prop_text(m.group(1))
    m = _SHOWS_RE.search(text)
    if m:
        return _normalize_prop_text(m.group(1))
    prop = extract_proposition_key(block)
    return _normalize_prop_text(prop) if prop else ""


def alpha_key_for_lemma_block(block: str) -> str:
    """基于完整陈述的 alpha 规范化键（保留变量在假设中的角色）。"""
    return alpha_normalize_proposition_key(extract_full_statement_text(block))


def build_lemma_merge_proposition_index(
    blocks: dict[str, str],
) -> tuple[dict[str, str], dict[str, str]]:
    """返回 (strict_prop -> name, alpha_prop -> name) 索引，仅含引理块。"""
    strict: dict[str, str] = {}
    alpha: dict[str, str] = {}
    for name, block in blocks.items():
        first = (block or "").strip().splitlines()[0] if block else ""
        if not _LEMMA_ONLY_KIND_RE.match(first):
            continue
        prop = extract_proposition_key(block)
        if not prop:
            continue
        strict.setdefault(prop, name)
        alpha.setdefault(alpha_key_for_lemma_block(block), name)
    return strict, alpha


def find_semantic_duplicate_name(
    block: str,
    *,
    strict_index: dict[str, str],
    alpha_index: dict[str, str],
) -> Optional[str]:
    prop = extract_proposition_key(block)
    if not prop:
        return None
    if prop in strict_index:
        return strict_index[prop]
    alpha = alpha_key_for_lemma_block(block)
    return alpha_index.get(alpha)


def rewrite_lemma_ref_names(block: str, alias_map: dict[str, str]) -> str:
    """将 proof 区域中的引理引用名按 alias_map 替换（保留 lemma 头行）。"""
    if not alias_map:
        return block
    lines = (block or "").splitlines()
    if not lines:
        return block
    head = lines[0]
    body = "\n".join(lines[1:])
    body = rewrite_lemma_names_in_text(body, alias_map)
    return head + ("\n" + body if body else "")


def rewrite_lemma_names_in_text(text: str, alias_map: dict[str, str]) -> str:
    """在任意 .thy 文本中将引理引用名按 alias_map 全局替换（含 sketch / final 定理）。"""
    if not alias_map or not text:
        return text
    out = text
    for old, new in sorted(alias_map.items(), key=lambda item: -len(item[0])):
        if not old or old == new:
            continue
        out = re.sub(rf"\b{re.escape(old)}\b", new, out)
    return out


def retarget_lemma_block_name(block: str, new_name: str) -> str:
    lines = (block or "").splitlines()
    if not lines or not new_name:
        return block
    lines[0] = re.sub(
        r"^(\s*(?:lemma|corollary|proposition)\s+)[A-Za-z0-9_']+",
        rf"\g<1>{new_name}",
        lines[0],
        count=1,
        flags=re.IGNORECASE,
    )
    return "\n".join(lines)


def topological_sort_lemma_block_names(
    blocks: dict[str, str],
    *,
    prefer_order: Optional[Sequence[str]] = None,
) -> List[str]:
    """
    按引理证明内的引用关系拓扑排序：被依赖者在前。
    出现环或未解析依赖时，按 prefer_order 稳定追加。
    """
    lemma_names: List[str] = []
    for name, block in blocks.items():
        first = (block or "").strip().splitlines()[0] if block else ""
        if _LEMMA_ONLY_KIND_RE.match(first):
            lemma_names.append(name)
    if not lemma_names:
        return []

    if prefer_order:
        base_order = {n: i for i, n in enumerate(prefer_order) if n in blocks}
    else:
        base_order = {n: i for i, n in enumerate(lemma_names)}

    prereqs: dict[str, set[str]] = {n: set() for n in lemma_names}
    for name in lemma_names:
        refs = collect_lemma_refs_from_proof(blocks[name])
        for ref in refs:
            if ref in blocks and ref in lemma_names and ref != name:
                prereqs[name].add(ref)

    sorted_names: List[str] = []
    remaining = set(lemma_names)
    while remaining:
        ready = [
            n
            for n in remaining
            if prereqs[n].issubset(set(sorted_names))
        ]
        if not ready:
            rest = sorted(remaining, key=lambda n: base_order.get(n, 10**9))
            sorted_names.extend(rest)
            break
        ready.sort(key=lambda n: base_order.get(n, 10**9))
        sorted_names.extend(ready)
        remaining -= set(ready)
    return sorted_names


def extract_proposition_key(lemma_text: str) -> Optional[str]:
    text = (lemma_text or "").strip()
    if not text:
        return None

    m = _SHOWS_RE.search(text)
    if m:
        return _normalize_prop_text(m.group(1))

    m = _ASSUMES_SHOWS_BLOCK_RE.search(text)
    if m:
        return _normalize_prop_text(m.group(1))

    head = _FACT_HEAD_RE.search(text)
    if head:
        after = text[head.end() :]
        qm = _PROP_IN_QUOTES_RE.search(after)
        if qm:
            return _normalize_prop_text(qm.group(1))

    quotes = _PROP_IN_QUOTES_RE.findall(text)
    if quotes:
        return _normalize_prop_text(max(quotes, key=len))

    return None


def extract_fact_name(lemma_text: str) -> Optional[str]:
    m = _FACT_HEAD_RE.search((lemma_text or "").strip())
    return m.group(2) if m else None


def _filter_lemma_ref_names(names: Set[str]) -> Set[str]:
    out: Set[str] = set()
    for name in names:
        if not name or name in _SKIP_PROOF_REF_NAMES:
            continue
        if len(name) == 1 and name.isalpha() and name.islower():
            continue
        out.add(name)
    return out


def collect_fact_names_from_sketch(sketch: str) -> Set[str]:
    names: Set[str] = set()
    for m in _FACT_HEAD_RE.finditer(sketch or ""):
        names.add(m.group(2))
    for m in _FACT_REF_RE.finditer(sketch or ""):
        names.add(m.group(1))
    for m in _BY_FACT_RE.finditer(sketch or ""):
        names.add(m.group(1))
    # 从 by (method arg1 arg2 ...) 括号中提取引理引用
    for m in _BY_PAREN_ARGS_RE.finditer(sketch or ""):
        args_text = m.group(1)
        # 先移除修饰前缀（add:/del: 等），再提取剩余标识符
        cleaned = _BY_MODIFIER_RE.sub(" ", args_text)
        for part in re.split(r"[\s,;]+", cleaned):
            part = part.strip().strip("'\"")
            if part and re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", part):
                names.add(part)
    for m in re.finditer(
        r"\busing\s+([A-Za-z0-9_',\s]+?)(?:\s+by|\s*$)",
        sketch or "",
        re.IGNORECASE | re.MULTILINE,
    ):
        for part in re.split(r"[\s,]+", m.group(1)):
            part = part.strip()
            if part and re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", part):
                names.add(part)
    for m in _SIMP_ADD_RE.finditer(sketch or ""):
        for part in re.split(r"[\s,]+", m.group(1)):
            part = part.strip()
            if part and re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", part):
                names.add(part)
    return names


def collect_lemma_refs_from_proof(proof_region: str) -> Set[str]:
    """从 proof 区域提取引理/事实引用名（已过滤 tactic 与局部 have）。"""
    return _filter_lemma_ref_names(collect_fact_names_from_sketch(proof_region))


def expand_lemma_ref_closure(
    root_refs: Set[str],
    blocks: dict[str, str],
) -> Set[str]:
    """展开引理依赖闭包：sketch 直接引用 + unproven 引理证明中的 transitive 引用。"""
    closure: Set[str] = set()
    pending = list(root_refs)
    while pending:
        name = pending.pop()
        if name in closure or name not in blocks:
            continue
        closure.add(name)
        sub_refs = collect_lemma_refs_from_proof(blocks[name])
        for ref in sub_refs:
            if ref in blocks and ref not in closure:
                pending.append(ref)
    return closure


def _should_keep_over(
    existing_name: str,
    new_name: str,
    sketch_refs: Set[str],
) -> bool:
    """是否用 new 替换已保留的 existing（同命题）。"""
    if new_name in sketch_refs and existing_name not in sketch_refs:
        return True
    return False


def dedupe_lemma_statements_detailed(
    statements: List[str],
    *,
    sketch: str = "",
) -> Tuple[List[str], List[dict]]:
    """去重并返回被丢弃的候选记录（含原因），供实验"生成漏斗"统计。

    reason 取值：
      - empty                    空/无效候选
      - text_duplicate           与已保留候选文本完全相同
      - same_proposition         与已保留候选命题相同、引理名不同
      - duplicate_name           引理名重复
      - same_proposition_replaced 被同命题候选替换（自身被移出）
    """
    sketch_refs = collect_fact_names_from_sketch(sketch)
    seen_text: set[str] = set()
    seen_names: set[str] = set()
    prop_key_to_index: dict[str, int] = {}
    deduped: List[str] = []
    dropped: List[dict] = []

    for stmt in statements:
        text = (stmt or "").strip()
        if not text:
            dropped.append({"name": "", "reason": "empty"})
            continue
        if text in seen_text:
            dropped.append(
                {
                    "name": extract_fact_name(text) or "",
                    "reason": "text_duplicate",
                }
            )
            continue

        name = extract_fact_name(text) or ""
        prop_key = extract_proposition_key(text)

        if prop_key and prop_key in prop_key_to_index:
            idx = prop_key_to_index[prop_key]
            old_name = extract_fact_name(deduped[idx]) or ""
            if name and _should_keep_over(old_name, name, sketch_refs):
                logger.info(
                    "语义重复引理：用 %s 替换 %s（命题相同，草图引用优先）",
                    name,
                    old_name,
                )
                if old_name:
                    seen_names.discard(old_name)
                seen_names.add(name)
                deduped[idx] = text
                dropped.append(
                    {
                        "name": old_name,
                        "reason": "same_proposition_replaced",
                        "kept_over": name,
                    }
                )
                continue
            logger.info(
                "跳过语义重复引理: %s（与 %s 同命题）",
                name or "?",
                old_name or "?",
            )
            dropped.append(
                {"name": name, "reason": "same_proposition", "kept_over": old_name}
            )
            continue

        if name and name in seen_names:
            logger.info("跳过重复引理名: %s", name)
            dropped.append({"name": name, "reason": "duplicate_name"})
            continue

        if name:
            seen_names.add(name)
        seen_text.add(text)
        if prop_key:
            prop_key_to_index[prop_key] = len(deduped)
        deduped.append(text)

    return deduped, dropped


def dedupe_lemma_statements(
    statements: List[str],
    *,
    sketch: str = "",
) -> List[str]:
    """去重后的候选引理（`dedupe_lemma_statements_detailed` 的只取保留集版本）。"""
    return dedupe_lemma_statements_detailed(statements, sketch=sketch)[0]


def ensure_pri_queue_invariant_lemmas(
    statements: List[str],
    theorem_data: Optional[dict] = None,
) -> List[str]:
    """
    pri_queue typedef 的不变式（distinct / sorted）常被 LLM 漏生成单独引理；
    主定理证明会引用 pri_queue_sorted，在此补全缺失项。
    """
    other = (theorem_data or {}).get("other formal") or ""
    if "pri_queue" not in other:
        return statements
    names = {extract_fact_name(s) for s in statements if extract_fact_name(s)}
    out = list(statements)
    if "pri_queue_sorted" not in names and "sorted (map snd" in other:
        out.append(
            'lemma pri_queue_sorted: "sorted (map snd (alist_of q))"\n  sorry'
        )
    if "pri_queue_distinct" not in names and "distinct (map fst" in other:
        out.append(
            'lemma pri_queue_distinct: "distinct (map fst (alist_of q))"\n  sorry'
        )
    return out


_LEMMA_ONLY_KIND_RE = re.compile(
    r"^\s*(lemma|corollary|proposition)\s+",
    re.IGNORECASE,
)
_THEOREM_KIND_RE = re.compile(r"^\s*theorem\s+", re.IGNORECASE)
_DECLARE_QAD_RE = re.compile(r"^\s*declare\s+\[\[quick_and_dirty", re.IGNORECASE)


def _strip_theory_shell_fragment(text: str) -> str:
    """去掉 LLM 误回显的 theory/imports/begin/end 外壳，只保留 begin 内正文。"""
    t = (text or "").strip()
    if not t:
        return ""
    t = re.sub(
        r"^\s*theory\s+[^\n]+\s*\nimports\s+[^\n]+\s*\nbegin\s*",
        "",
        t,
        count=1,
        flags=re.MULTILINE | re.IGNORECASE | re.DOTALL,
    )
    t = re.sub(r"\n\s*end\s*\Z", "", t.strip(), flags=re.IGNORECASE)
    t = "\n".join(ln for ln in t.splitlines() if ln.strip().lower() != "end")
    return t.strip()


def split_non_main_facts_from_sketch(
    sketch: str,
    main_theorem_name: str,
) -> Tuple[str, str]:
    """
    从 LLM proof 字段拆出误放的引理块，只保留主定理片段。
    返回 (main_fragment, extra_lemma_blocks)。
    """
    from ..eval.proof_difficulty_score_v2.thy_extract import extract_decl_blocks

    sk = _strip_theory_shell_fragment(sketch)
    if not sk:
        return "", ""

    wrapped = f'theory "_split"\nimports Main\nbegin\n\n{sk}\n\nend\n'
    blocks = extract_decl_blocks(wrapped)

    extra_parts: List[str] = []
    main_theorem_block: Optional[str] = None

    for name, block in blocks.items():
        if _LEMMA_ONLY_KIND_RE.match(block):
            extra_parts.append(block)
        elif _THEOREM_KIND_RE.match(block):
            if name == main_theorem_name:
                main_theorem_block = block
            else:
                logger.warning(
                    "proof 字段含非主定理 theorem %s，已丢弃",
                    name,
                )
        else:
            extra_parts.append(block)

    if main_theorem_block:
        main = main_theorem_block.strip() + "\n"
    else:
        main = extract_sketch_main_theorem(sk, main_theorem_name)

    extra = "\n\n".join(extra_parts).strip()
    return main, (extra + "\n") if extra else ""


def extract_sketch_main_theorem(sketch: str, main_theorem_name: str) -> str:
    """
    从草图/LLM 输出中只保留一条主定理（同名取最后一段），并去掉 theory/end 外壳与孤立的 end 行。
    避免 merge 后出现「end 之后又跟一整段 theorem」的非法 .thy。
    """
    sk = (sketch or "").strip()
    if not sk:
        return ""

    sk = re.sub(
        r"^\s*theory\s+[^\n]+\s*\nimports\s+[^\n]+\s*\nbegin\s*",
        "",
        sk,
        count=1,
        flags=re.MULTILINE | re.IGNORECASE | re.DOTALL,
    )
    sk = re.sub(r"\n\s*end\s*\Z", "", sk.strip(), flags=re.IGNORECASE)
    sk = "\n".join(ln for ln in sk.splitlines() if ln.strip().lower() != "end")

    for kind in ("theorem", "lemma", "corollary", "proposition"):
        pat = re.compile(
            rf"(^\s*{kind}\s+{re.escape(main_theorem_name)}\b.*?)"
            rf"(?=^\s*(?:theorem|lemma|corollary|proposition)\s+|\Z)",
            re.MULTILINE | re.DOTALL | re.IGNORECASE,
        )
        matches = list(pat.finditer(sk))
        if matches:
            return matches[-1].group(1).strip() + "\n"
    return sk.strip() + "\n" if sk.strip() else ""


def truncate_theory_to_first_closure(text: str) -> str:
    """只保留第一个 theory begin … end 闭包，丢弃 end 之后的残留（重复 theorem 等）。"""
    lines = (text or "").splitlines()
    if not lines:
        return ""
    out: List[str] = []
    seen_begin = False
    for line in lines:
        out.append(line)
        if re.match(r"^\s*begin\s*$", line):
            seen_begin = True
        elif seen_begin and re.match(r"^\s*end\s*$", line):
            break
    result = "\n".join(out).strip("\n")
    return result + "\n" if result else ""


def strip_extra_fact_declarations(
    content: str,
    *,
    main_theorem_name: str,
    injected_fact_names: Set[str],
) -> str:
    if not (content or "").strip():
        return content

    lines = content.splitlines()
    out: List[str] = []
    i = 0
    n = len(lines)

    while i < n:
        line = lines[i]
        m = _FACT_HEAD_RE.match(line)
        if not m:
            out.append(line)
            i += 1
            continue

        kind, fname = m.group(1).lower(), m.group(2)
        is_main_theorem = kind == "theorem" and fname == main_theorem_name

        if not is_main_theorem and fname in injected_fact_names:
            logger.info(
                "从草图中移除重复 fact 声明: %s %s（已在预注入引理中）",
                kind,
                fname,
            )
            i += 1
            while i < n:
                if _FACT_HEAD_RE.match(lines[i]):
                    break
                if lines[i].strip() == "end":
                    break
                i += 1
            continue

        out.append(line)
        i += 1

    result = "\n".join(out).strip("\n")
    return result + "\n" if result else ""


def strip_quick_and_dirty_declarations(text: str) -> str:
    """去掉 quick_and_dirty 声明（仅 sketch/unproven 验证阶段使用，不应出现在 final .thy）。"""
    if not (text or "").strip():
        return text
    lines = [
        ln for ln in text.splitlines() if not _DECLARE_QAD_RE.match(ln)
    ]
    result = "\n".join(lines).strip("\n")
    return result + "\n" if result else ""


def merge_sketch_into_theory(
    sketch: str,
    theorem_name: str,
    injected_fact_names: Set[str],
) -> str:
    sk = (sketch or "").strip()
    if not sk:
        return ""

    # 先抽出唯一主定理块（草图修复 LLM 可能回显整份 .thy 或多段 theorem+end）
    body = extract_sketch_main_theorem(sk, theorem_name)
    if not body.strip():
        body = sk
        if f'theory "{theorem_name}"' in sk or f"theory {theorem_name}" in sk:
            begin_match = re.search(r"begin\s+(.*?)\s+end", sk, re.DOTALL)
            body = begin_match.group(1) if begin_match else sk
        body = "\n".join(
            ln for ln in body.splitlines() if ln.strip().lower() != "end"
        )

    return strip_extra_fact_declarations(
        body,
        main_theorem_name=theorem_name,
        injected_fact_names=injected_fact_names,
    )


_DECL_HEAD_FOR_MAIN_RE = re.compile(
    r"(?m)^([ \t]*)(theorem|lemma|corollary|proposition)([ \t]+)([A-Za-z_][\w'.]*)"
)
_ISABELLE_FENCE_ONLY_RE = re.compile(
    r"```\s*(?:isabelle)?\s*\n?(.*?)```", re.DOTALL | re.IGNORECASE
)


def ensure_main_theorem_declaration(
    body: str,
    theorem_statement: str,
    theorem_name: str,
) -> str:
    """
    论文 2.2.2 / 图 2-4：形式化草图可能只输出证明体（没有 theorem 头）。
    此时用形式化定理陈述补出主定理声明；若模型改写了主定理名，则纠正回 theorem_name。
    """
    text = (body or "").strip()
    if not text:
        return text

    decls = list(_DECL_HEAD_FOR_MAIN_RE.finditer(text))
    if decls:
        first = decls[0]
        kind = first.group(2).lower()
        if first.group(4) != theorem_name and (kind == "theorem" or len(decls) == 1):
            text = text[: first.start(4)] + theorem_name + text[first.end(4):]
        return text + ("\n" if not text.endswith("\n") else "")

    stmt = (theorem_statement or "").strip()
    fence = _ISABELLE_FENCE_ONLY_RE.search(stmt)
    if fence:
        stmt = (fence.group(1) or "").strip()
    if not stmt:
        return text
    if not stmt.endswith("\n"):
        stmt += "\n"
    return stmt + text + "\n"
