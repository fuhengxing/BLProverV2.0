"""引理库总览导出（results/proven_lemmas/lemma_library.json）。

论文口径
--------
2.4   引理库以 Isabelle 理论文件承载，按被成功证明的先后顺序组织；
      （2.4.1）已证明引理存储为「引理陈述 + 完整形式化证明 + 唯一递增标识符」。
3.1.1 证明推导难度 D(i) = |Reach(i)| + |Edge(i)|（依赖闭包节点数 + 依赖边数）。
3.1.2 跨定理复用性 U(i) = 1 + u(i)（1 为自身基础价值，u(i) 为库内直接调用者数）。
3.1.3 语法复杂度 S(i) = 语法树节点数/深度/量词与连接词数/变量数 的加权和。
3.1.4 综合质量评分 Q(i) = D(i) * U(i) / S(i)（收益成本比）。
3.2.1 来源标签（global/middle/repair）与线性标签（四类 + nonlinear）。
3.2.2 差异化衰减 Delta_i = Delta_0 * 来源系数 * 线性系数；Q 逐批次衰减。
3.2.3 淘汰阈值 Qmin：Q(i) < Qmin 的引理移出引理库。
4.1.2 引理库复用率 = 被引用的留存引理数 / 留存引理总数（引理级）。
      主口径仅统计「被定理证明引用」的留存引理；库内引理之间的调用作为副口径另行给出。

本模块把分散在 results/proven_lemmas/ 与 results/lemma_classification/ 下的元数据
汇总为单文件，逐条记录引理陈述、形式化证明、被调用次数、存活周期与引理质量，
便于快速掌握引理库的总体情况。
"""

from __future__ import annotations

import json
import re
import textwrap
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence

from .lemma_classification import (
    ALL_LEMMAS_FILENAME,
    INDEX_FILENAME as CLASSIFICATION_INDEX_FILENAME,
    STATUS_ELIMINATED,
    STATUS_IN_LIBRARY,
    STATUS_PENDING,
    UNKNOWN_SOURCE,
    classification_root,
    load_lemma_blocks,
)
from .quality_screening import linear_coefficient, source_coefficient

PROVEN_SUBDIR = "proven_lemmas"
LIBRARY_FILENAME = "lemma_library.json"
LIFECYCLE_FILENAME = "lemma_lifecycle.json"
SCHEMA_VERSION = "lemma-library/v1"

_SYNTAX_FILENAME = "lemma_quality_latest.json"
_SCORES_FILENAME = "lemma_quality_scores.json"
_SCREENING_FILENAME = "quality_screening.json"
_DEPENDENCY_FILENAME = "dependency_graph.json"
_IDENTIFIERS_TEMPLATE = "lemma_identifiers_{domain}.json"

FIELD_NOTES: Dict[str, str] = {
    "id": "证明先后顺序标识符（论文 2.4.1 唯一递增标识）",
    "statement": "引理陈述（形式化声明）",
    "proof": "引理的形式化证明脚本体",
    "source": "来源标签：global/middle/repair（论文 2.3）",
    "source_coefficient": "来源系数（论文表 3-2）",
    "linear_labels": "线性标签：序列不变性/操作可执行性/递归终止性/序关系保持性（论文 3.2.1）",
    "linear_coefficient": "线性系数，多标签取最小（论文表 3-3）",
    "quality.q": "Q(i) = Q_SCALE * D(i)*U(i)/S(i)（论文 3.1.4；Q_SCALE=100 放大标定，见 eval/quality_scale.py）",
    "quality.q_base": "本批次评分前的 Q(i)（未叠加历史衰减）",
    "quality.d": "D(i) 证明推导难度 = 依赖闭包节点数 + 依赖边数（论文 3.1.1）",
    "quality.u": "U(i) 跨定理复用性 = 1 + 库内直接调用者数（论文 3.1.2）",
    "quality.s": "S(i) 语法复杂度（论文 3.1.3）",
    "quality.decay": "Delta_i = 1.0 * 来源系数 * 线性系数（论文 3.2.2；Δ0 = 标定值 0.01 × Q_SCALE 100）",
    "call.call_count": "被库内其它引理直接调用的次数 u(i)（论文 3.1.2）",
    "call.callers": "直接调用本引理的库内引理名列表",
    "call.theorem_references": "在定理证明中引用了本引理的定理名列表",
    "call.total_call_count": "被调用总次数 = 库内引理调用 + 定理引用",
    "lifecycle.survival_batches": "存活周期：引理在库中已存活的批次数（论文 3.2.2 生命周期）",
    "lifecycle.first_batch": "首次入库（被成功证明并纳入引理库）的批次",
    "lifecycle.eliminated_batch": "被淘汰的批次（未淘汰为 null）",
    "status": "in_library 留存 / eliminated 已淘汰 / pending 已登记未证",
    "reuse.library_lemmas": "论文 4.1.2 复用率分母：留存引理（有证明且未淘汰）总数",
    "reuse.referenced_library_lemmas": "论文 4.1.2 复用率分子：留存引理中被定理证明引用的条数（仅定理引用）",
    "reuse.reuse_rate": "论文 4.1.2 主口径引理库复用率 = 被定理引用的留存引理数 / 留存引理总数",
    "reuse.reuse_rate_any_reference": "副口径复用率：库内引理调用或定理引用，任一即计入分子",
}

_PROOF_START_RE = re.compile(
    r"^\s*(?:proof|by|apply|done|qed|using|unfolding|hence|thus|have|show|"
    r"obtain|from|with|then|moreover|ultimately|also|finally|let|assume|"
    r"presume|note|case|next)\b"
)
_INLINE_PROOF_RE = re.compile(r"\s(?:by|proof|apply)\s")
_CLASS_BLOCK_RE = re.compile(
    r"^\(\* ==== ([A-Za-z0-9_']+)(?:[^\n]*?)==== \*\)$", re.MULTILINE
)
_LEMMA_DECL_RE = re.compile(r"^\s*(?:lemma|corollary|proposition)\b")


def library_dir(output_dir: str | Path) -> Path:
    return Path(output_dir) / "results" / PROVEN_SUBDIR


def library_json_path(output_dir: str | Path) -> Path:
    return library_dir(output_dir) / LIBRARY_FILENAME


def lifecycle_path(output_dir: str | Path) -> Path:
    return library_dir(output_dir) / LIFECYCLE_FILENAME


def _load_json(path: Path, default: object) -> object:
    if not path.is_file():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def blocks_from_classification_thy(text: str) -> Dict[str, str]:
    """????? .thy ???????lemma_blocks.json ????????"""
    if not text:
        return {}
    parts = _CLASS_BLOCK_RE.split(text)
    out: Dict[str, str] = {}
    for idx in range(1, len(parts) - 1, 2):
        name = parts[idx]
        body = parts[idx + 1].split("\nend")[0].strip()
        if name and body and name not in out and _LEMMA_DECL_RE.match(body):
            out[name] = body
    return out


def split_statement_proof(block: str) -> Dict[str, str]:
    """把一个引理块拆成陈述与证明两部分。"""
    text = (block or "").strip()
    if not text:
        return {"statement": "", "proof": ""}
    lines = text.split("\n")
    for idx, line in enumerate(lines):
        if _PROOF_START_RE.match(line):
            return {
                "statement": "\n".join(lines[:idx]).rstrip(),
                "proof": textwrap.dedent("\n".join(lines[idx:])).rstrip(),
            }
    head = lines[0]
    match = _INLINE_PROOF_RE.search(head)
    while match is not None:
        if head[: match.start()].count('"') % 2 == 0:
            return {
                "statement": head[: match.start()].rstrip(),
                "proof": "\n".join([head[match.start() + 1 :].rstrip()] + lines[1:]).rstrip(),
            }
        match = _INLINE_PROOF_RE.search(head, match.end())
    return {"statement": text, "proof": ""}


_SORRY_RE = re.compile(r"\bsorry\b")
_LEMMA_NAME_RE = re.compile(
    r"^\s*(?:lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)


def strip_sorry_lines(text: str) -> str:
    """删除单独的 ``sorry`` 行（未证明引理只保留陈述）。"""
    lines = [
        line
        for line in (text or "").splitlines()
        if not re.fullmatch(r"\s*sorry\s*", line)
    ]
    return "\n".join(lines).rstrip()


_ISABELLE_SYMBOLS = {
    "≤": "\\<le>",
    "≥": "\\<ge>",
    "≠": "\\<noteq>",
    "¬": "\\<not>",
    "∧": "\\<and>",
    "∨": "\\<or>",
    "⟶": "\\<longrightarrow>",
    "→": "\\<longrightarrow>",
    "⟹": "\\<Longrightarrow>",
    "⇒": "\\<Longrightarrow>",
    "∀": "\\<forall>",
    "∃": "\\<exists>",
    "∈": "\\<in>",
    "∉": "\\<notin>",
    "×": "\\<times>",
    "⊆": "\\<subseteq>",
    "∪": "\\<union>",
    "∩": "\\<inter>",
    "∘": "\\<circ>",
    "·": "\\<cdot>",
}


def normalize_isabelle_symbols(text: str) -> str:
    """把 JSON 阶段数组里的 Unicode 数学符号转成 Isabelle ASCII 转义。"""
    out = text or ""
    for symbol, escape in _ISABELLE_SYMBOLS.items():
        out = out.replace(symbol, escape)
    return out


def recover_statements_from_results(output_dir: str | Path) -> Dict[str, str]:
    """从 results/<theorem>/result.json 的各阶段引理数组还原未入库引理陈述。

    被语义去重丢弃（dedup_dropped）或只在阶段数组中出现的候选引理，
    不会进入 lemma_blocks.json，但在 result.json 的阶段数组里仍有完整陈述。
    """
    root = Path(output_dir) / "results"
    recovered: Dict[str, str] = {}
    if not root.is_dir():
        return recovered
    for result_path in sorted(root.glob("*/result.json")):
        try:
            data = json.loads(result_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(data, dict):
            continue
        for key in ("lemmas_stage1", "lemmas_stage3", "constructed_lemma_statements"):
            items = data.get(key)
            if not isinstance(items, list):
                continue
            for item in items:
                text = str(item or "").strip()
                if not text:
                    continue
                match = _LEMMA_NAME_RE.search(text)
                if not match:
                    continue
                recovered.setdefault(
                    match.group(1), normalize_isabelle_symbols(text)
                )
    return recovered


def load_lifecycle(output_dir: str | Path) -> Dict[str, object]:
    """读取引理生命周期状态（批次、存活周期、历史评分、引用记录）。"""
    data = _load_json(lifecycle_path(output_dir), {})
    if not isinstance(data, dict):
        data = {}
    data.setdefault("batch_index", 0)
    data.setdefault("domain", "")
    data.setdefault("lemmas", {})
    if not isinstance(data.get("lemmas"), dict):
        data["lemmas"] = {}
    return data


def save_lifecycle(output_dir: str | Path, data: Mapping[str, object]) -> Path:
    path = lifecycle_path(output_dir)
    _write_json(path, data)
    return path


def update_lifecycle(
    output_dir: str | Path,
    *,
    domain: str,
    theorem_name: str = "",
    lemma_names: Iterable[str] = (),
    q_by_lemma: Optional[Mapping[str, float]] = None,
    eliminated: Iterable[str] = (),
    callers_by_lemma: Optional[Mapping[str, Sequence[str]]] = None,
    referenced_by_theorem: Iterable[str] = (),
) -> Dict[str, object]:
    """推进一个批次：登记新引理、累计 Q 历史与引用记录、记录存活周期。"""
    state = load_lifecycle(output_dir)
    batch = int(state.get("batch_index") or 0) + 1
    state["batch_index"] = batch
    if domain:
        state["domain"] = str(domain)
    lemmas: Dict[str, dict] = state["lemmas"]  # type: ignore[assignment]

    eliminated_set = {str(n) for n in eliminated}
    q_map = {str(k): float(v) for k, v in (q_by_lemma or {}).items()}
    callers_map = {str(k): list(v) for k, v in (callers_by_lemma or {}).items()}
    theorem_refs = {str(n) for n in referenced_by_theorem}

    for name in lemma_names:
        name = str(name)
        row = lemmas.get(name)
        if not isinstance(row, dict):
            row = {
                "first_batch": batch,
                "eliminated_batch": None,
                "quality_history": [],
                "theorem_references": [],
                "callers": [],
            }
            lemmas[name] = row
        row["last_batch"] = batch
        row["survival_batches"] = batch - int(row.get("first_batch") or batch) + 1
        if name in q_map:
            history = row.setdefault("quality_history", [])
            history.append({"batch": batch, "q": round(q_map[name], 6)})
        if name in callers_map:
            row["callers"] = sorted(set(callers_map[name]))
        if name in theorem_refs and theorem_name:
            refs = row.setdefault("theorem_references", [])
            if theorem_name not in refs:
                refs.append(theorem_name)
        if name in eliminated_set and row.get("eliminated_batch") is None:
            row["eliminated_batch"] = batch
            row["status"] = STATUS_ELIMINATED
        elif name not in eliminated_set:
            row["status"] = STATUS_IN_LIBRARY

    save_lifecycle(output_dir, state)
    return state


def _syntax_details(output_dir: str | Path) -> Dict[str, dict]:
    report = _load_json(library_dir(output_dir) / _SYNTAX_FILENAME, {})
    out: Dict[str, dict] = {}
    if not isinstance(report, dict):
        return out
    syntax = report.get("syntax_complexity")
    if not isinstance(syntax, dict):
        return out
    stage = syntax.get("stage1") or {}
    items = stage.get("items") if isinstance(stage, dict) else None
    for item in items or []:
        if not isinstance(item, dict):
            continue
        name = str(item.get("lemma_name") or "")
        if not name:
            continue
        out[name] = {
            "s": item.get("s"),
            "nodes": item.get("prop_nodes"),
            "depth": item.get("depth"),
            "quant_conn": item.get("quant_conn"),
            "var_count": item.get("var_count"),
        }
    return out


def _ordered_names(
    index: Mapping[str, object],
    blocks: Mapping[str, str],
    scores: Mapping[str, object],
    identifiers: Mapping[str, object],
) -> List[str]:
    names: List[str] = []
    seen: set[str] = set()
    for source in (identifiers, blocks, scores, index):
        for name in source:
            key = str(name)
            if key and key not in seen:
                names.append(key)
                seen.add(key)
    names.sort(key=lambda n: (int(identifiers.get(n) or 10 ** 6), n))
    return names


def build_library_document(
    output_dir: str | Path,
    *,
    domain: str = "",
    theorem_name: str = "",
    paper: object = None,
    lifecycle: Optional[Mapping[str, object]] = None,
) -> Dict[str, object]:
    """汇总引理库总览（论文 2.4 / 3.1 / 3.2 / 4.1.2）。"""
    out_path = Path(output_dir)
    cls_root = classification_root(out_path)
    index = _load_json(cls_root / CLASSIFICATION_INDEX_FILENAME, {})
    if not isinstance(index, dict):
        index = {}
    blocks: Dict[str, str] = dict(load_lemma_blocks(cls_root))
    all_thy_path = cls_root / ALL_LEMMAS_FILENAME
    if all_thy_path.is_file():
        try:
            fallback_blocks = blocks_from_classification_thy(
                all_thy_path.read_text(encoding="utf-8")
            )
        except OSError:
            fallback_blocks = {}
        for name, text in fallback_blocks.items():
            blocks.setdefault(name, text)
    recovered = recover_statements_from_results(out_path)
    scores = _load_json(library_dir(out_path) / _SCORES_FILENAME, {})
    if not isinstance(scores, dict):
        scores = {}
    screening = _load_json(library_dir(out_path) / _SCREENING_FILENAME, {})
    if not isinstance(screening, dict):
        screening = {}
    dependency = _load_json(library_dir(out_path) / _DEPENDENCY_FILENAME, {})
    if not isinstance(dependency, dict):
        dependency = {}
    identifiers = _load_json(
        library_dir(out_path) / _IDENTIFIERS_TEMPLATE.format(domain=domain or "unknown"),
        {},
    )
    if not isinstance(identifiers, dict):
        identifiers = {}
    syntax = _syntax_details(out_path)
    state = dict(lifecycle or load_lifecycle(out_path))
    state_lemmas = state.get("lemmas") if isinstance(state.get("lemmas"), dict) else {}

    src_coeffs = getattr(getattr(paper, "source_coefficient", None), "copy", None)
    lin_coeffs = getattr(getattr(paper, "linear_coefficient", None), "copy", None)
    src_coeffs = src_coeffs() if callable(src_coeffs) else None
    lin_coeffs = lin_coeffs() if callable(lin_coeffs) else None

    rows: List[Dict[str, object]] = []
    for name in _ordered_names(index, blocks, scores, identifiers):
        entry = index.get(name)
        entry = dict(entry) if isinstance(entry, dict) else {}
        score = scores.get(name)
        score = dict(score) if isinstance(score, dict) else {}
        dep = dependency.get(name)
        dep = dict(dep) if isinstance(dep, dict) else {}
        syn = syntax.get(name) or {}
        life = state_lemmas.get(name)
        life = dict(life) if isinstance(life, dict) else {}
        trusted_block = blocks.get(name) or ""
        block = trusted_block or recovered.get(name) or ""
        parts = split_statement_proof(block)
        if not (parts.get("statement") or "").strip():
            # 未证/待证引理可能只登记在 classification index 中（无引理块），
            # 用 index 的 statement_preview 兜底，保证“全部生成引理”可追溯。
            preview = str(entry.get("statement_preview") or "").strip()
            if preview:
                parts = split_statement_proof(preview)
        if not trusted_block and block:
            # 阶段数组里的候选引理带 sorry：只保留陈述，不算“已证明”。
            parts = {
                "statement": strip_sorry_lines(parts.get("statement") or ""),
                "proof": "",
            }

        source = str(score.get("source") or entry.get("source") or UNKNOWN_SOURCE)
        labels = score.get("linear_labels") or entry.get("linear_labels") or []
        if isinstance(labels, str):
            labels = [labels]
        labels = [str(x) for x in labels]

        callers = [str(x) for x in (dep.get("callers") or life.get("callers") or [])]
        theorem_refs = [str(x) for x in (life.get("theorem_references") or [])]
        if not theorem_refs and int(dep.get("theorem_ref_count") or 0) > 0 and theorem_name:
            theorem_refs = [theorem_name]

        status = str(entry.get("status") or (life.get("status") or STATUS_PENDING))
        eliminated = status == STATUS_ELIMINATED or bool(score.get("eliminated"))

        d_value = score.get("d", dep.get("d"))
        u_value = score.get("u", dep.get("u"))
        s_value = score.get("s", syn.get("s"))
        rows.append(
            {
                "id": identifiers.get(name),
                "name": name,
                "source": source,
                "source_coefficient": round(
                    source_coefficient(source, src_coeffs), 4
                ),
                "linear_labels": labels,
                "linear_coefficient": round(
                    linear_coefficient(labels, lin_coeffs), 4
                ),
                "statement": parts["statement"],
                "proof": parts["proof"],
                "has_proof": bool(parts["proof"]),
                "quality": {
                    "q": score.get("q"),
                    "q_base": score.get("q_base"),
                    "d": d_value,
                    "u": u_value,
                    "s": s_value,
                    "decay": score.get("delta"),
                    "below_qmin": score.get("below_qmin"),
                },
                "syntax_complexity": {
                    "nodes": syn.get("nodes"),
                    "depth": syn.get("depth"),
                    "quant_conn": syn.get("quant_conn"),
                    "var_count": syn.get("var_count"),
                },
                "proof_difficulty": {
                    "reach": list(dep.get("reach") or []),
                    "edge_count": dep.get("edge_count"),
                    "direct": list(dep.get("direct") or []),
                    "is_leaf": dep.get("is_leaf"),
                },
                "call": {
                    "call_count": len(callers),
                    "callers": callers,
                    "theorem_references": theorem_refs,
                    "total_call_count": len(callers) + len(theorem_refs),
                },
                "status": status,
                "eliminated": eliminated,
                "lifecycle": {
                    "first_batch": life.get("first_batch"),
                    "survival_batches": life.get("survival_batches"),
                    "eliminated_batch": life.get("eliminated_batch"),
                    "quality_history": list(life.get("quality_history") or []),
                },
                "domain": str(entry.get("domain") or domain or ""),
                "first_seen_theorem": str(entry.get("first_seen_theorem") or ""),
            }
        )

    retained = [r for r in rows if r["status"] != STATUS_ELIMINATED and r["has_proof"]]
    referenced = [r for r in retained if int(r["call"]["total_call_count"]) > 0]
    theorem_referenced = [
        r for r in retained if r["call"]["theorem_references"]
    ]
    q_values = [
        float(r["quality"]["q"])
        for r in rows
        if r["quality"]["q"] is not None
    ]
    eliminated_rows = [r for r in rows if r["eliminated"]]

    def _tally(key: str) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for row in rows:
            values = row[key] if key == "linear_labels" else [row[key]]
            for value in values or [UNKNOWN_SOURCE]:
                counts[str(value)] = counts.get(str(value), 0) + 1
        return dict(sorted(counts.items()))

    def _rate(numerator: int, denominator: int) -> float:
        return round(numerator / denominator, 4) if denominator else 0.0

    with_proof = sum(1 for r in rows if r["has_proof"])
    summary = {
        "generated_total": with_proof,
        "registered_total": len(rows),
        "library_total": len(retained),
        "eliminated_total": len(eliminated_rows),
        "elimination_rate": _rate(len(eliminated_rows), len(rows)),
        "reuse": {
            # 论文 4.1.2 主口径：分子仅统计「被定理证明引用」的留存引理
            "library_lemmas": len(retained),
            "referenced_library_lemmas": len(theorem_referenced),
            "reuse_rate": _rate(len(theorem_referenced), len(retained)),
            "reused_lemma_names": sorted(str(r["name"]) for r in theorem_referenced),
            # 副口径：库内引理之间的调用也计入（仅作对比，不作论文口径）
            "referenced_library_lemmas_any": len(referenced),
            "reuse_rate_any_reference": _rate(len(referenced), len(retained)),
            "reused_lemma_names_any": sorted(str(r["name"]) for r in referenced),
        },
        "quality": {
            "mean": round(sum(q_values) / len(q_values), 6) if q_values else None,
            "max": round(max(q_values), 6) if q_values else None,
            "min": round(min(q_values), 6) if q_values else None,
        },
        "call_count_total": sum(int(r["call"]["total_call_count"]) for r in rows),
        "with_proof": with_proof,
        "by_source": _tally("source"),
        "by_linear_label": _tally("linear_labels"),
        "by_status": _tally("status"),
    }

    return {
        "schema": SCHEMA_VERSION,
        "domain": domain,
        "theorem": theorem_name,
        "batch_index": state.get("batch_index"),
        "output_dir": str(out_path),
        "metrics_notes": FIELD_NOTES,
        "summary": summary,
        "lemmas": rows,
    }


def write_library_json(
    output_dir: str | Path,
    *,
    domain: str = "",
    theorem_name: str = "",
    paper: object = None,
    lifecycle: Optional[Mapping[str, object]] = None,
) -> Path:
    document = build_library_document(
        output_dir,
        domain=domain,
        theorem_name=theorem_name,
        paper=paper,
        lifecycle=lifecycle,
    )
    path = library_json_path(output_dir)
    _write_json(path, document)
    return path


def record_batch_and_export(
    output_dir: str | Path,
    *,
    domain: str = "",
    theorem_name: str = "",
    paper: object = None,
    advance_batch: bool = True,
) -> Path:
    """???????????????????????? lemma_library.json?"""
    document = build_library_document(
        output_dir, domain=domain, theorem_name=theorem_name, paper=paper
    )
    if advance_batch:
        rows = document["lemmas"]
        lifecycle = update_lifecycle(
            output_dir,
            domain=domain,
            theorem_name=theorem_name,
            lemma_names=[r["name"] for r in rows if r["has_proof"]],
            q_by_lemma={
                r["name"]: r["quality"]["q"]
                for r in rows
                if r["quality"]["q"] is not None
            },
            eliminated=[r["name"] for r in rows if r["eliminated"]],
            callers_by_lemma={r["name"]: r["call"]["callers"] for r in rows},
            referenced_by_theorem=[
                r["name"] for r in rows if r["call"]["theorem_references"]
            ],
        )
        document = build_library_document(
            output_dir,
            domain=domain,
            theorem_name=theorem_name,
            paper=paper,
            lifecycle=lifecycle,
        )
    path = library_json_path(output_dir)
    _write_json(path, document)
    return path
