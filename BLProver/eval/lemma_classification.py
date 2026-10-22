"""
论文 3.2.1 / 第 5 章实验指标：引理来源标签与线性标签的分类归档。

在 `results/lemma_classification/` 下建立分类文件夹，便于后续按来源/线性标签统计：

    lemma_classification/
      index.json                     # 每条引理：来源、线性标签、状态、首次定理
      summary.json                   # 各来源 / 各线性标签的计数
      by_source/<source>/lemmas.json # global / middle / repair / unknown
      by_linear_label/<label>/lemmas.json
                                     # sequence_invariance / operation_executability
                                     # recursion_termination / order_preservation / nonlinear

- 来源标签（论文 3.2.1(1)）：global / middle / repair。
- 线性标签（论文 3.2.1(2)）：四类线性数据结构特性，不属于者记 nonlinear（多标签全部记录）。
- 分类目录跨批次累积：已淘汰引理保留在目录中并标记 status=eliminated。
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from .quality_screening import (
    LINEAR_LABELS,
    SOURCE_LABELS,
    SOURCE_MIDDLE,
    identify_linear_labels,
)

CLASSIFICATION_DIRNAME = "lemma_classification"
INDEX_FILENAME = "index.json"
SUMMARY_FILENAME = "summary.json"
LEMMAS_FILENAME = "lemmas.json"
ALL_LEMMAS_FILENAME = "all_lemmas.thy"
CLASSIFICATION_NOTE = "BLProver lemma classification export"
BLOCKS_FILENAME = "lemma_blocks.json"
UNKNOWN_SOURCE = "unknown"

_LEMMA_DECL_RE = re.compile(r"^\s*(lemma|corollary|proposition)\b", re.IGNORECASE)

STATUS_IN_LIBRARY = "in_library"
STATUS_ELIMINATED = "eliminated"
STATUS_PENDING = "pending"


def classification_root(output_dir: str | Path) -> Path:
    return Path(output_dir) / "results" / CLASSIFICATION_DIRNAME


def _thy_stem(label: str) -> str:
    """Isabelle requires theory name == file stem, so emit <label>_lemmas."""
    safe = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in (label or ""))
    return f"{safe or 'unknown'}_lemmas"


def _render_classification_thy(
    *,
    theory_name: str,
    class_label: str,
    domain: str,
    theorem_name: str,
    definitions_block: str,
    blocks: Sequence[Tuple[str, str]],
    statuses: Mapping[str, str],
    unproven: Sequence[str],
) -> str:
    """Render a self-contained .thy: imports Main + domain defs + selected lemma blocks."""
    lines: List[str] = [
        f'theory "{theory_name}"',
        "imports Main",
        "begin",
        "",
        "(* -------------------------------------------------------------------- *)",
        f"(* {CLASSIFICATION_NOTE}",
        f"   class     : {class_label}",
        f"   domain    : {domain or '(unknown)'}",
        f"   theorem   : {theorem_name or '(unknown)'}",
        f"   lemmas    : {len(blocks)} with proof, {len(unproven)} without recorded proof",
        "   index     : results/lemma_classification/index.json",
        "*)",
        "(* -------------------------------------------------------------------- *)",
        "",
    ]
    if definitions_block.strip():
        lines.append("(* ==== domain definitions ==== *)")
        lines.append(definitions_block.strip())
        lines.append("")
    else:
        lines.append(
            "(* WARNING: no definitions block supplied; this file may not check. *)"
        )
        lines.append("")
    for name, text in blocks:
        status = (statuses.get(name) or "").strip()
        suffix = f" (status: {status})" if status else ""
        lines.append(f"(* ==== {name}{suffix} ==== *)")
        lines.append(text.strip())
        lines.append("")
    if unproven:
        lines.append("(* ==== lemmas without a recorded proof (listed only) ==== *)")
        for name in unproven:
            lines.append(f"(* {name} *)")
        lines.append("")
    lines.append("end")
    lines.append("")
    return "\n".join(lines)


def _write_group_thy(
    path: Path,
    *,
    theory_name: str,
    class_label: str,
    domain: str,
    theorem_name: str,
    definitions_block: str,
    order: Sequence[str],
    group_names: Iterable[str],
    lemma_blocks: Mapping[str, str],
    statuses: Mapping[str, str],
) -> Optional[Path]:
    members = set(group_names)
    primary, extras = _with_dependencies(members, order, lemma_blocks)
    wanted = primary | extras
    blocks = [(n, lemma_blocks[n]) for n in order if n in wanted]
    unproven = [n for n in order if n in members and n not in lemma_blocks]
    if not blocks and not unproven:
        return None
    local_statuses = dict(statuses)
    for name in extras:
        base = (statuses.get(name) or "").strip()
        local_statuses[name] = (
            f"{base}, included as dependency" if base else "included as dependency"
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        _render_classification_thy(
            theory_name=theory_name,
            class_label=class_label,
            domain=domain,
            theorem_name=theorem_name,
            definitions_block=definitions_block,
            blocks=blocks,
            statuses=local_statuses,
            unproven=unproven,
        ),
        encoding="utf-8",
        newline="\n",
    )
    return path


def _is_lemma_block(text: str) -> bool:
    """只把 lemma/corollary/proposition 视为引理；theorem 在 <定理>.thy 中已单独产出。"""
    return bool(_LEMMA_DECL_RE.match(text or ""))


def _with_dependencies(
    group: Iterable[str],
    order: Sequence[str],
    blocks: Mapping[str, str],
) -> Tuple[set, set]:
    """
    返回 (本组引理, 依赖引理)。分类导出按标签分组后，组内引理的证明可能引用他组引理，
    为保证每个 .thy 能被 Isabelle 直接检查通过，这里把被引用的引理一并带入并标注。
    """
    available = [name for name in order if name in blocks]
    primary = {name for name in group if name in blocks}
    wanted = set(primary)
    changed = True
    while changed:
        changed = False
        for name in list(wanted):
            text = blocks.get(name) or ""
            for other in available:
                if other in wanted or other == name:
                    continue
                pattern = r"(?<![A-Za-z0-9_'])" + re.escape(other) + r"(?![A-Za-z0-9_'])"
                if re.search(pattern, text):
                    wanted.add(other)
                    changed = True
    return primary, wanted - primary


def write_classification_theories(
    root: str | Path,
    *,
    domain: str = "",
    theorem_name: str = "",
    lemma_blocks: Optional[Mapping[str, str]] = None,
    block_order: Optional[Sequence[str]] = None,
    definitions_block: str = "",
) -> List[Path]:
    """
    Export the classification archive as Isabelle theories that can be opened directly.

    - all_lemmas.thy                              : every lemma (with proof)
    - by_source/<source>/<source>_lemmas.thy      : by source label (global/middle/repair/...)
    - by_linear_label/<label>/<label>_lemmas.thy  : by linear label

    Lemma order follows ``block_order`` (order of appearance in source .thy files) so that
    inter-lemma dependencies are accepted by Isabelle; only lemma names present in
    ``index.json`` are exported, and lemmas without a recorded proof are listed as comments.
    """
    root = Path(root)
    index = _load_json(root / INDEX_FILENAME, {})
    if not isinstance(index, dict):
        index = {}
    provided = {
        str(name): str(text)
        for name, text in (lemma_blocks or {}).items()
        if str(text).strip() and _is_lemma_block(str(text))
    }
    blocks = load_lemma_blocks(root)
    blocks.update(provided)
    statuses = {
        str(name): str(entry.get("status") or "")
        for name, entry in index.items()
        if isinstance(entry, Mapping)
    }

    order: List[str] = []
    seen: set[str] = set()
    for name in list(block_order or []) + sorted(index.keys()):
        if name and name not in seen:
            order.append(name)
            seen.add(name)

    written: List[Path] = []
    all_path = _write_group_thy(
        root / ALL_LEMMAS_FILENAME,
        theory_name="all_lemmas",
        class_label="all",
        domain=domain,
        theorem_name=theorem_name,
        definitions_block=definitions_block,
        order=order,
        group_names=sorted(index.keys()),
        lemma_blocks=blocks,
        statuses=statuses,
    )
    if all_path:
        written.append(all_path)

    # ?? 4.1.2?????????????????
    #   retained_lemmas.thy   ???????????
    #   eliminated_lemmas.thy ??????????????????
    def _names_by_status(target: str, keep: bool) -> List[str]:
        picked: List[str] = []
        for name, entry in index.items():
            status = str(entry.get("status") or "") if isinstance(entry, Mapping) else ""
            if (status == target) if keep else (status != target):
                picked.append(str(name))
        return picked

    for theory_name, class_label, names in (
        ("retained_lemmas", "retained", _names_by_status(STATUS_ELIMINATED, False)),
        ("eliminated_lemmas", "eliminated", _names_by_status(STATUS_ELIMINATED, True)),
    ):
        path = _write_group_thy(
            root / f"{theory_name}.thy",
            theory_name=theory_name,
            class_label=class_label,
            domain=domain,
            theorem_name=theorem_name,
            definitions_block=definitions_block,
            order=order,
            group_names=names,
            lemma_blocks=blocks,
            statuses=statuses,
        )
        if path:
            written.append(path)

    for source in list(SOURCE_LABELS) + [UNKNOWN_SOURCE]:
        names = [
            name
            for name, entry in index.items()
            if str(entry.get("source") or UNKNOWN_SOURCE) == source
        ]
        path = _write_group_thy(
            root / "by_source" / source / f"{_thy_stem(source)}.thy",
            theory_name=_thy_stem(source),
            class_label=f"by_source/{source}",
            domain=domain,
            theorem_name=theorem_name,
            definitions_block=definitions_block,
            order=order,
            group_names=names,
            lemma_blocks=blocks,
            statuses=statuses,
        )
        if path:
            written.append(path)

    for label in LINEAR_LABELS:
        names = [
            name
            for name, entry in index.items()
            if label in list(entry.get("linear_labels") or [])
        ]
        path = _write_group_thy(
            root / "by_linear_label" / label / f"{_thy_stem(label)}.thy",
            theory_name=_thy_stem(label),
            class_label=f"by_linear_label/{label}",
            domain=domain,
            theorem_name=theorem_name,
            definitions_block=definitions_block,
            order=order,
            group_names=names,
            lemma_blocks=blocks,
            statuses=statuses,
        )
        if path:
            written.append(path)

    return written


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
        json.dumps(payload, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8",
    )


def load_lemma_blocks(root: str | Path) -> Dict[str, str]:
    """读取历史归档的带证明引理块（跨批次累积，含已被淘汰的引理）。"""
    payload = _load_json(Path(root) / BLOCKS_FILENAME, {})
    if not isinstance(payload, dict):
        return {}
    raw = payload.get("blocks")
    if not isinstance(raw, dict):
        raw = payload
    return {
        str(k): str(v)
        for k, v in raw.items()
        if str(v).strip() and _is_lemma_block(str(v))
    }


def record_lemma_blocks(root: str | Path, blocks: Mapping[str, str]) -> Path:
    """归档带证明的引理块；同名以本次为准，历史条目保留（淘汰引理仍可查看）。"""
    root = Path(root)
    merged = load_lemma_blocks(root)
    for name, text in (blocks or {}).items():
        if name and str(text).strip() and _is_lemma_block(str(text)):
            merged[str(name)] = str(text)
    path = root / BLOCKS_FILENAME
    _write_json(
        path,
        {
            "blocks": merged,
        },
    )
    return path


def _preview(text: str, limit: int = 200) -> str:
    one_line = " ".join((text or "").split())
    return one_line[:limit]


def update_classification(
    output_dir: str | Path,
    *,
    domain: str = "",
    theorem_name: str = "",
    scores: Optional[Mapping[str, Mapping[str, object]]] = None,
    labels: Optional[Mapping[str, Mapping[str, object]]] = None,
    statements: Optional[Mapping[str, str]] = None,
    eliminated: Optional[Iterable[str]] = None,
    lemma_blocks: Optional[Mapping[str, str]] = None,
    block_order: Optional[Sequence[str]] = None,
    definitions_block: str = "",
) -> Path:
    """
    更新引理分类归档（跨批次累积）。

    :param scores: {name: {source, linear_labels, ...}}（质量筛选产物）
    :param labels: {name: {source, linear_labels}}（lemma_labels.json）
    :param statements: {name: 引理块文本}，用于生成陈述预览
    :param eliminated: 本批次被淘汰（移出引理库）的引理名
    :param lemma_blocks: {name: 带证明的引理块文本}，用于导出可打开的 .thy（默认取 statements）
    :param block_order: 引理块在源 .thy 中的出现顺序，保证导出 .thy 的依赖顺序
    :param definitions_block: 领域定义块（typedef/definition），导出 .thy 自包含所需
    """
    root = classification_root(output_dir)
    root.mkdir(parents=True, exist_ok=True)
    index_path = root / INDEX_FILENAME
    index = _load_json(index_path, {})
    if not isinstance(index, dict):
        index = {}

    scores = scores or {}
    labels = labels or {}
    statements = statements or {}
    eliminated_set = set(eliminated or ())

    names: List[str] = []
    for src in (scores, labels, statements):
        for name in src:
            if name and name not in names:
                names.append(name)

    for name in names:
        score_row = scores.get(name) or {}
        label_row = labels.get(name) or {}
        entry = dict(index.get(name) or {})

        source = (
            str(score_row.get("source") or "")
            or str(label_row.get("source") or "")
            or entry.get("source")
            or UNKNOWN_SOURCE
        )
        linear = (
            list(score_row.get("linear_labels") or [])
            or list(label_row.get("linear_labels") or [])
            or list(entry.get("linear_labels") or [])
        )
        if not linear:
            stmt = statements.get(name, "")
            if stmt:
                linear = identify_linear_labels(stmt)

        if name in eliminated_set:
            status = STATUS_ELIMINATED
        elif name in scores or name in statements:
            status = STATUS_IN_LIBRARY
        else:
            status = STATUS_PENDING

        entry.update(
            {
                "source": source,
                "linear_labels": linear,
                "status": status,
                "domain": domain or entry.get("domain", ""),
            }
        )
        entry["has_proof"] = bool(
            name in (lemma_blocks or {})
            or name in scores
            or bool(entry.get("has_proof"))
        )
        label_origin = (
            str(score_row.get("linear_label_source") or "")
            or str(label_row.get("linear_label_source") or "")
            or str(entry.get("linear_label_source") or "")
        )
        if label_origin:
            entry["linear_label_source"] = label_origin
        if theorem_name:
            entry.setdefault("first_seen_theorem", theorem_name)
            entry.setdefault("first_seen_theorems", [])
            if theorem_name not in entry["first_seen_theorems"]:
                entry["first_seen_theorems"].append(theorem_name)
        stmt = statements.get(name)
        if stmt:
            entry["statement_preview"] = _preview(stmt)
        index[name] = entry

    _write_json(index_path, index)

    by_source: Dict[str, List[dict]] = {src: [] for src in SOURCE_LABELS}
    by_source[UNKNOWN_SOURCE] = []
    by_linear: Dict[str, List[dict]] = {label: [] for label in LINEAR_LABELS}

    for name, entry in sorted(index.items()):
        row = {
            "name": name,
            "source": entry.get("source", UNKNOWN_SOURCE),
            "linear_labels": list(entry.get("linear_labels") or []),
            "status": entry.get("status", STATUS_PENDING),
            "domain": entry.get("domain", ""),
        }
        if entry.get("linear_label_source"):
            row["linear_label_source"] = entry["linear_label_source"]
        if entry.get("statement_preview"):
            row["statement_preview"] = entry["statement_preview"]
        by_source.setdefault(row["source"], []).append(row)
        for label in row["linear_labels"]:
            by_linear.setdefault(label, []).append(row)

    for source, rows in by_source.items():
        _write_json(root / "by_source" / source / LEMMAS_FILENAME, rows)
        if not rows:
            _write_json(root / "by_source" / source / LEMMAS_FILENAME, [])
    for label, rows in by_linear.items():
        _write_json(root / "by_linear_label" / label / LEMMAS_FILENAME, rows)

    summary = {
        "domain": domain,
        "total": len(index),
        "by_source": {k: len(v) for k, v in sorted(by_source.items())},
        "by_linear_label": {k: len(v) for k, v in sorted(by_linear.items())},
        "by_status": {},
    }
    for entry in index.values():
        st = str(entry.get("status") or STATUS_PENDING)
        summary["by_status"][st] = summary["by_status"].get(st, 0) + 1
    eliminated_total = summary["by_status"].get(STATUS_ELIMINATED, 0)
    total = len(index)
    summary["libraries"] = {
        "all": total,
        "retained": total - eliminated_total,
        "eliminated": eliminated_total,
        "elimination_rate": round(eliminated_total / total, 4) if total else 0.0,
        "all_thy": ALL_LEMMAS_FILENAME,
        "retained_thy": "retained_lemmas.thy",
        "eliminated_thy": "eliminated_lemmas.thy",
    }
    _write_json(root / SUMMARY_FILENAME, summary)

    record_lemma_blocks(
        root, lemma_blocks if lemma_blocks is not None else (statements or {})
    )
    write_classification_theories(
        root,
        domain=domain,
        theorem_name=theorem_name,
        lemma_blocks=lemma_blocks if lemma_blocks is not None else statements,
        block_order=block_order,
        definitions_block=definitions_block,
    )
    return root
