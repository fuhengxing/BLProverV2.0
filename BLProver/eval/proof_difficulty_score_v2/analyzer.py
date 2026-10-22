"""
证明中显式引用的引理/事实名提取与去重计数（flat used-lemma count）。

规则：扫描 proof / by 区域内的 using、unfolding、simp add/del、metis 等，
提取标识符并去重；排除本地 have 名（h1…）、assms、case 标签及 Isabelle 关键字。
"""

from __future__ import annotations

import re
from typing import FrozenSet, List, Set, Tuple

# 不参与计数的标识（小写比较）
_EXCLUDE_EXACT: FrozenSet[str] = frozenset(
    {
        "assms",
        "this",
        "that",
        "then",
        "hence",
        "thus",
        "from",
        "with",
        "of",
        "in",
        "if",
        "let",
        "shows",
        "fixes",
        "assumes",
        "proof",
        "qed",
        "done",
        "oops",
        "sorry",
        "next",
        "case",
        "True",
        "False",
        "show",
        "have",
        "using",
        "unfolding",
        "simp",
        "add",
        "del",
        "only",
        "metis",
        "auto",
        "blast",
        "fastforce",
        "force",
        "clarsimp",
        "smt",
        "rule",
        "erule",
        "drule",
        "frule",
        "intro",
        "elim",
        "dest",
        "where",
        "for",
        "types",
        "lifting",
        "no_types",
        "opaque",
        "unfold",
        "fold",
        "arith",
        "presburger",
        "linarith",
        "simp_all",
        "simp_all_simps",
        "open",
        "close",
        "thesis",
        "thesis_concl",
        "concl",
        "hyps",
        "prems",
        "goal",
        "context",
        "structure",
        "type_synonym",
        "definition",
        "lemma",
        "theorem",
        "corollary",
        "fun",
        "primrec",
    }
)

# tactic 子句匹配（捕获引用列表）
_TACTIC_RES: Tuple[re.Pattern[str], ...] = tuple(
    re.compile(p, re.IGNORECASE)
    for p in (
        r"\busing\s+([^;\n]+)",
        r"\bunfolding\s+([^;\n]+)",
        r"\bsimp\s+add\s*:\s*([^;\n]+)",
        r"\bsimp\s+del\s*:\s*([^;\n]+)",
        r"\bsimp\s+only\s*:\s*([^;\n]+)",
        r"\bmetis\s*(?:\([^)]*\))?\s+([^;\n]+)",
        r"\bauto\s+(?:simp\s+add\s*:\s*)?([^;\n]+)",
        r"\bclarsimp\s+(?:simp\s+add\s*:\s*)?([^;\n]+)",
        r"\bfastforce\s+(?:simp\s+add\s*:\s*)?([^;\n]+)",
        r"\bforce\s+(?:simp\s+add\s*:\s*)?([^;\n]+)",
        r"\bby\s*\(\s*(?:rule|erule|drule|frule|intro|elim|dest)\s+([^)]+)\)",
        r"\bby\s*\(\s*simp\s+add\s*:\s*([^)]+)\)",
        r"\bby\s*\(\s*metis\s*(?:\([^)]*\))?\s+([^)]+)\)",
    )
)

_PROOF_START_RE = re.compile(
    r"^\s*(proof\b|apply\b|by\s|oops\b|sorry\b)",
    re.IGNORECASE | re.MULTILINE,
)

_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*")

_LOCAL_HAVE_RE = re.compile(r"^h\d+$", re.IGNORECASE)
# obtain 局部绑定：ys_def、zs_split 等（1–2 字母前缀；不含 min_def 等库定义）
_LOCAL_OBTAIN_RE = re.compile(
    r"^[a-z]{1,2}_(?:def|split|eq|inv)$", re.IGNORECASE
)
# 常见单字母/短变量名
_SHORT_VAR_NAMES: FrozenSet[str] = frozenset(
    {"p", "n", "m", "k", "v", "q", "f", "g", "h", "x", "y", "z", "xs", "ys", "zs"}
)


def _strip_isabelle_antiquotes(text: str) -> str:
    """去掉 simp add: \\<open>...\\<close> 中的项，避免 open/close 等误识别。"""
    s = text or ""
    s = re.sub(r"\\<open>.*?\\<close>", " ", s, flags=re.DOTALL)
    s = re.sub(r"<open>.*?</close>", " ", s, flags=re.DOTALL)
    return s


def _looks_like_lemma_name(name: str) -> bool:
    """启发式：库引理/定理名通常含 '_' 或 '.'。"""
    if not name:
        return False
    if "_" in name or "." in name:
        return True
    if name.endswith("_simps") or name.endswith("def"):
        return True
    return False


def _normalize_lemma_token(raw: str) -> str:
    """option.distinct(1) -> option.distinct；Scratch.min_def -> min_def（保留最后一段）。"""
    t = (raw or "").strip()
    if not t:
        return ""
    # 去掉外层括号
    while t.startswith("(") and t.endswith(")"):
        t = t[1:-1].strip()
    # 去掉 (2) 这类下标
    t = re.sub(r"\(\d+\)\s*$", "", t).strip()
    if "." in t:
        parts = t.split(".")
        if len(parts) >= 2 and parts[-1].replace("_", "").isalnum():
            return parts[-1]
    return t


def _should_exclude(name: str) -> bool:
    if not name:
        return True
    low = name.lower()
    if low in _EXCLUDE_EXACT:
        return True
    if _LOCAL_HAVE_RE.match(name):
        return True
    if _LOCAL_OBTAIN_RE.match(name):
        return True
    if low in _SHORT_VAR_NAMES:
        return True
    if name[0].isupper() and name in ("True", "False"):
        return True
    if not _looks_like_lemma_name(name):
        return True
    return False


def _tokens_from_clause(clause: str) -> List[str]:
    clause = _strip_isabelle_antiquotes(clause)
    out: List[str] = []
    for m in _TOKEN_RE.finditer(clause or ""):
        norm = _normalize_lemma_token(m.group(0))
        if norm and not _should_exclude(norm):
            out.append(norm)
    return out


def extract_proof_region(text: str) -> str:
    """从引理/定理块中提取 proof / by 区域（若无则返回全文）。"""
    src = text or ""
    m = _PROOF_START_RE.search(src)
    if m:
        return src[m.start() :]
    return src


_HAVE_NAME_RE = re.compile(
    r"\b(?:then\s+)?have\s+([A-Za-z][A-Za-z0-9_']*)",
    re.IGNORECASE,
)

_DECL_HEAD_RE = re.compile(
    r"^\s*(lemma|theorem|corollary)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE | re.MULTILINE,
)


def parse_decl_name(text: str, *, default: str = "unknown") -> str:
    """从文本首条 lemma/theorem/corollary 声明解析名称。"""
    m = _DECL_HEAD_RE.search(text or "")
    if m:
        return m.group(2)
    return default


def _local_have_names(text: str) -> Set[str]:
    """本证明内 have 引入的局部事实名（不计入库引理）。"""
    names: Set[str] = set()
    for m in _HAVE_NAME_RE.finditer(text or ""):
        names.add(_normalize_lemma_token(m.group(1)))
    return {n for n in names if n}


def extract_used_lemma_names(text: str) -> List[str]:
    """
    从证明文本提取显式引用的引理名（去重、按在证明中出现的先后顺序）。

    同一引理只保留第一次出现的位置。
    """
    region = extract_proof_region(text)
    local_haves = _local_have_names(text)
    # (在 proof 区域中的偏移, 子句内序号, 引理名)
    events: List[Tuple[int, int, str]] = []
    for pat in _TACTIC_RES:
        for m in pat.finditer(region):
            clause = m.group(m.lastindex or 1)
            pos = m.start()
            for idx, tok in enumerate(_tokens_from_clause(clause)):
                if tok in local_haves:
                    continue
                events.append((pos, idx, tok))
    events.sort(key=lambda x: (x[0], x[1]))
    ordered: List[str] = []
    seen: Set[str] = set()
    for _pos, _idx, tok in events:
        if tok in seen:
            continue
        seen.add(tok)
        ordered.append(tok)
    return ordered


def count_used_lemmas_in_text(text: str) -> Tuple[int, List[str]]:
    names = extract_used_lemma_names(text)
    return len(names), names


def count_used_lemmas(statement: str) -> Tuple[int, List[str]]:
    """对单条构造引理 statement 统计 used lemma 数量。"""
    return count_used_lemmas_in_text(statement)
