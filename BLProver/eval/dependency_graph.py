"""
论文 3.1.1 / 3.1.2：证明依赖图（D(i) 依赖闭包）与 U(i) 直接调用者。

- 节点：已证明引理库中的引理/定理声明。
- 有向边 i -> j：证明 i 时**直接调用** j（仅统计库内引理，命中标准库/局部 have 的不计入）。
- Reach(i)：从 i 沿依赖边可达的全部不同节点（不含 i 自身）。
- Edge(i)：依赖子图中的全部边 = 从 i 出发的直接边 + Reach(i) 中每个节点的直接边。
- D(i) = 1（叶子：Reach(i) 与 Edge(i) 均空）否则 |Reach(i)| + |Edge(i)|（论文 3.1.1）。
- u(i) = 直接调用 i 的库内引理集合；U(i) = 1 + |u(i)|（仅直接调用者，不沿链上溯，论文 3.1.2）。
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Set

from .proof_difficulty_score_v2.analyzer import extract_used_lemma_names
from .proof_difficulty_score_v2.thy_extract import extract_decl_blocks
from ..utils.lemma_dedup import collect_lemma_refs_from_proof


def library_direct_dependencies(decls: Dict[str, str]) -> Dict[str, Set[str]]:
    """为库内每个声明计算直接依赖集合 d(i)（仅保留库内引理名）。"""
    known = set(decls.keys())
    direct: Dict[str, Set[str]] = {}
    for name, block in decls.items():
        refs: Set[str] = set(extract_used_lemma_names(block))
        try:
            refs.update(collect_lemma_refs_from_proof(block))
        except Exception:
            pass
        refs.discard(name)
        direct[name] = {r for r in refs if r in known}
    return direct


def reach_of(direct: Dict[str, Set[str]], node: str) -> Set[str]:
    """Reach(i)：从 node 出发沿依赖边可达的所有不同节点（不含 node 自身）。"""
    seen: Set[str] = set()
    stack: List[str] = list(direct.get(node, ()))
    while stack:
        cur = stack.pop()
        if cur in seen or cur == node:
            continue
        seen.add(cur)
        stack.extend(direct.get(cur, ()))
    return seen


def compute_d(direct: Dict[str, Set[str]], node: str) -> Dict[str, object]:
    """论文 3.1.1：D(i) = 1（叶子）否则 |Reach(i)| + |Edge(i)|。"""
    reach = reach_of(direct, node)
    edge_count = len(direct.get(node, ()))
    for n in reach:
        edge_count += len(direct.get(n, ()))
    is_leaf = not reach and edge_count == 0
    d_value = 1 if is_leaf else len(reach) + edge_count
    return {
        "d": d_value,
        "direct": sorted(direct.get(node, ())),
        "reach": sorted(reach),
        "reach_count": len(reach),
        "edge_count": edge_count,
        "is_leaf": is_leaf,
    }


def compute_u(direct: Dict[str, Set[str]], node: str) -> Dict[str, object]:
    """论文 3.1.2：U(i) = 1 + |u(i)|，u(i) 为库内直接调用 i 的引理集合。"""
    callers = sorted(n for n, deps in direct.items() if node in deps and n != node)
    return {"u": 1 + len(callers), "callers": callers}


def analyze_library(
    decls: Dict[str, str],
    *,
    theorem_texts: Optional[Iterable[str]] = None,
) -> Dict[str, Dict[str, object]]:
    """
    汇总库内每条引理的 D/U 与依赖信息。

    theorem_texts：定理证明文本（非库内节点）；仅用于附带统计"被定理直接引用"的次数，
    不参与 U(i)（论文 3.1.2 明确 U 只统计库内直接调用者）。
    """
    direct = library_direct_dependencies(decls)
    theorem_refs: Set[str] = set()
    for text in theorem_texts or ():
        theorem_refs.update(extract_used_lemma_names(text))
        try:
            theorem_refs.update(collect_lemma_refs_from_proof(text))
        except Exception:
            pass

    out: Dict[str, Dict[str, object]] = {}
    for name in decls:
        info = compute_d(direct, name)
        info.update(compute_u(direct, name))
        info["theorem_ref_count"] = 1 if name in theorem_refs else 0
        out[name] = info
    return out


def analyze_thy_text(
    thy_text: str,
    *,
    theorem_texts: Optional[Iterable[str]] = None,
) -> Dict[str, Dict[str, object]]:
    """从 proven_lemmas.thy 文本直接分析（库节点 + 可选定理文本）。"""
    decls = extract_decl_blocks(thy_text or "")
    return analyze_library(decls, theorem_texts=theorem_texts)


def d_scores(analysis: Dict[str, Dict[str, object]]) -> Dict[str, int]:
    return {name: int(info["d"]) for name, info in analysis.items()}


def u_scores(analysis: Dict[str, Dict[str, object]]) -> Dict[str, int]:
    return {name: int(info["u"]) for name, info in analysis.items()}
