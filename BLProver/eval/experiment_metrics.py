"""
论文 4.1.2 评估指标：从运行产物汇总实验指标（第 5 章）。

四个维度：
1. 引理生成效率   —— 三类来源策略产出的候选引理总量（读 `results/lemma_classification/`）
2. 引理筛选有效性 —— 引理淘汰率（淘汰数 / 候选引理总数）
3. 引理库复用率   —— 被定理证明引用的留存引理数 / 留存引理总数（论文 4.1.2 主口径：仅定理引用）
4. 定理证明成功率 —— 通过 Isabelle 内核校验（无 sorry/oops/错误）的定理占比

只读产物、只写报告，不修改任何证明产物。
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence

from .lemma_classification import (
    ALL_LEMMAS_FILENAME,
    INDEX_FILENAME,
    STATUS_ELIMINATED,
    UNKNOWN_SOURCE,
    classification_root,
)

METRICS_DIRNAME = "experiment_metrics"

SOURCE_KEYS = ("global", "middle", "repair", "unknown")
_LINEAR_KEYS = (
    "sequence_invariance",
    "operation_executability",
    "recursion_termination",
    "order_preservation",
    "nonlinear",
)

_VERIFIED_STATUSES = {"theorem_and_used_lemmas_verified"}


def metrics_root(output_dir: str | Path) -> Path:
    return Path(output_dir) / "results" / METRICS_DIRNAME


def _load_json(path: Path, default: object) -> object:
    if not path.is_file():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def _lemma_names_in_thy(text: str) -> set[str]:
    return set(re.findall(r"^\s*(?:lemma|theorem)\s+([A-Za-z_][\w']*)", text or "", re.M))


def _library_names(output_dir: Path, domain: str) -> set[str]:
    from ..lemma.proven_lemma_store import ProvenLemmaStore

    try:
        path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
    except Exception:
        return set()
    if not path.is_file():
        return set()
    try:
        return _lemma_names_in_thy(path.read_text(encoding="utf-8"))
    except OSError:
        return set()


def _proven_lemma_names(output_dir: str | Path) -> set[str]:
    """分类归档 all_lemmas.thy 中的引理名（只有真正带证明的引理才会写入该文件）。"""
    path = classification_root(output_dir) / ALL_LEMMAS_FILENAME
    if not path.is_file():
        return set()
    try:
        return _lemma_names_in_thy(path.read_text(encoding="utf-8"))
    except OSError:
        return set()


def collect_metrics(
    output_dir: str | Path,
    *,
    data_dir: Optional[str | Path] = None,
) -> Dict[str, object]:
    """汇总论文 4.1.2 的四项实验指标。"""
    out = Path(output_dir)
    results_dir = out / "results"

    # --- 定理层 ---
    index = _load_json(classification_root(out) / INDEX_FILENAME, {})
    if not isinstance(index, dict):
        index = {}
    archived_lemmas = set(index.keys())
    # 论文 4.1.2-3：分母为「留存引理」数 = 已证明且未被淘汰的引理。
    # 分类归档里的 status 是「最近一批」的状态：in_library = 本批重新打分通过，
    # pending = 在库但本批未重新打分（仍属留存），eliminated = 已淘汰。
    # 旧口径只认 in_library，会漏掉 pending 的留存引理，使 metrics.md 与交付包
    # index.json / library.json 的口径互相矛盾（留存数被低估、复用率失真）。
    proven_names = _proven_lemma_names(out)
    retained_lemmas: set[str] = {
        str(name)
        for name, entry in index.items()
        if isinstance(entry, Mapping)
        and str(entry.get("status") or "") != STATUS_ELIMINATED
        and (
            # New indexes record has_proof; a pending lemma that was never
            # proved must not be counted as retained.
            bool(entry.get("has_proof")) if "has_proof" in entry
            else (not proven_names or str(name) in proven_names)
        )
    }
    # Legacy snapshots (no has_proof field) cannot tell pending from retained,
    # so keep the old fallback; new snapshots must trust retained_lemmas even
    # when it is empty, otherwise unproven pendings inflate the reuse denominator.
    has_proof_flag = any(
        "has_proof" in entry for entry in index.values() if isinstance(entry, Mapping)
    )
    library_lemmas = (
        retained_lemmas if (retained_lemmas or has_proof_flag) else archived_lemmas
    )
    referenced_library: set[str] = set()

    per_theorem: List[Dict[str, object]] = []
    proven = 0
    attempted = 0
    reusing = 0
    if results_dir.is_dir():
        for result_file in sorted(results_dir.glob("*/result.json")):
            data = _load_json(result_file, {})
            if not isinstance(data, dict):
                continue
            name = str(data.get("theorem_name") or result_file.parent.name)
            status = str(data.get("status") or "")
            verified = bool(data.get("final_theorem_verified")) or status in _VERIFIED_STATUSES
            domain = str(data.get("domain") or result_file.parent.name)
            attempted += 1
            # 论文 4.1.2 主口径：分子只统计定理证明直接引用的留存引理（仅定理引用，不含引理间调用）
            # 与"当前库 ∪ 分类归档（含已淘汰）"取交集，避免筛选淘汰后失真
            library = _library_names(out, _domain_of(data)) | library_lemmas
            usage = data.get("lemma_usage") or {}
            if isinstance(usage, dict):
                referenced = set(usage.get("used_lemma_names") or []) | set(
                    usage.get("external_ref_names") or []
                )
            else:
                referenced = set()
            hit = sorted(referenced & library) if library else sorted(referenced)
            if verified:
                proven += 1
                # 论文 4.1.2-3：只有命中的是「留存引理」才算该定理复用了引理库；
                # 引用未证明的 pending 引理不计入分子（否则分母为 0 会出现 1.0 的假复用率）。
                if referenced & library_lemmas:
                    reusing += 1
                referenced_library.update(referenced & library_lemmas)
            per_theorem.append(
                {
                    "theorem_name": name,
                    "status": status,
                    "verified": verified,
                    "referenced_lemmas": hit,
                }
            )

    dataset_total = 0
    if data_dir:
        dataset_total = len(list(Path(data_dir).glob("*.json")))

    # --- 引理层（读分类归档）---
    by_source = {k: 0 for k in SOURCE_KEYS}
    by_linear = {k: 0 for k in _LINEAR_KEYS}
    by_status: Dict[str, int] = {}
    for entry in index.values():
        if not isinstance(entry, Mapping):
            continue
        src = str(entry.get("source") or UNKNOWN_SOURCE)
        by_source[src] = by_source.get(src, 0) + 1
        for label in entry.get("linear_labels") or []:
            by_linear[label] = by_linear.get(label, 0) + 1
        st = str(entry.get("status") or "pending")
        by_status[st] = by_status.get(st, 0) + 1

    lemma_total = len(index)
    eliminated = by_status.get(STATUS_ELIMINATED, 0)
    # 留存 = 已证明且未淘汰；待证 = 已登记但尚无证明（不含已淘汰的）
    retained = len(retained_lemmas)
    pending = max(lemma_total - eliminated - retained, 0)

    metrics: Dict[str, object] = {
        "output_dir": str(out),
        "theorem_proving": {
            "dataset_total": dataset_total,
            "attempted": attempted,
            "proven": proven,
            "success_rate_attempted": round(proven / attempted, 4) if attempted else 0.0,
            "success_rate_dataset": round(proven / dataset_total, 4) if dataset_total else 0.0,
            "per_theorem": per_theorem,
        },
        "lemma_generation_efficiency": {
            "total": lemma_total,
            "by_source": by_source,
            "by_linear_label": by_linear,
        },
        "lemma_screening_effectiveness": {
            "candidates": lemma_total,
            "retained": retained,
            "eliminated": eliminated,
            "pending": pending,
            "elimination_rate": round(eliminated / lemma_total, 4) if lemma_total else 0.0,
        },
        "lemma_library_reuse": {
            "library_lemmas": len(library_lemmas),
            "referenced_library_lemmas": len(referenced_library),
            "reuse_rate": round(len(referenced_library) / len(library_lemmas), 4)
            if library_lemmas
            else 0.0,
            "reused_lemma_count": len(referenced_library),
            "reused_lemma_names": sorted(referenced_library),
            "proven_theorems": proven,
            "proven_theorems_reusing_library": reusing,
            "theorem_reuse_rate": round(reusing / proven, 4) if proven else 0.0,
        },
    }
    return metrics


def _domain_of(data: Mapping) -> str:
    return str(data.get("domain") or "").strip()


def render_markdown(metrics: Mapping[str, object]) -> str:
    tp = metrics.get("theorem_proving") or {}
    gen = metrics.get("lemma_generation_efficiency") or {}
    scr = metrics.get("lemma_screening_effectiveness") or {}
    reuse = metrics.get("lemma_library_reuse") or {}
    lines: List[str] = []
    lines.append("# 实验指标汇总（论文 4.1.2）")
    lines.append("")
    lines.append("")
    lines.append("## 1. 引理生成效率")
    lines.append("")
    lines.append(f"- 候选引理总数：**{gen.get('total', 0)}**")
    lines.append("")
    lines.append("| 来源 | 数量 |")
    lines.append("| --- | --- |")
    for key, value in (gen.get("by_source") or {}).items():
        lines.append(f"| {key} | {value} |")
    lines.append("")
    lines.append("| 线性标签 | 数量 |")
    lines.append("| --- | --- |")
    for key, value in (gen.get("by_linear_label") or {}).items():
        lines.append(f"| {key} | {value} |")
    lines.append("")
    lines.append("## 2. 引理筛选有效性")
    lines.append("")
    lines.append(
        f"- 候选 {scr.get('candidates', 0)}，留存 {scr.get('retained', 0)}，"
        f"淘汰 {scr.get('eliminated', 0)}，待证 {scr.get('pending', 0)}"
    )
    lines.append(f"- 淘汰率：**{scr.get('elimination_rate', 0.0)}**")
    lines.append("")
    lines.append("## 3. 引理库复用率")
    lines.append("")
    lines.append(
        f"- 留存引理 {reuse.get('library_lemmas', 0)} 条，其中被定理证明引用 "
        f"{reuse.get('referenced_library_lemmas', 0)} 条（主口径：仅定理引用）"
    )
    lines.append(
        f"- 引理库复用率（论文 4.1.2 主口径：仅定理引用）：**{reuse.get('reuse_rate', 0.0)}**"
    )
    lines.append(
        f"- 成功证明定理 {reuse.get('proven_theorems', 0)} 条，其中引用自定义引理库 "
        f"{reuse.get('proven_theorems_reusing_library', 0)} 条"
        f"（定理级复用率 {reuse.get('theorem_reuse_rate', 0.0)}）"
    )
    lines.append(f"- 被复用的引理数：{reuse.get('reused_lemma_count', 0)}")
    lines.append("")
    lines.append("## 4. 定理证明成功率")
    lines.append("")
    lines.append(
        f"- 数据集定理数 {tp.get('dataset_total', 0)}，已尝试 {tp.get('attempted', 0)}，"
        f"成功 {tp.get('proven', 0)}"
    )
    lines.append(f"- 成功率（按尝试）：**{tp.get('success_rate_attempted', 0.0)}**")
    lines.append(f"- 成功率（按数据集）：**{tp.get('success_rate_dataset', 0.0)}**")
    lines.append("")
    return "\n".join(lines)


def write_metrics(output_dir: str | Path, metrics: Mapping[str, object]) -> Path:
    root = metrics_root(output_dir)
    root.mkdir(parents=True, exist_ok=True)
    (root / "metrics.json").write_text(
        json.dumps(metrics, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8",
    )
    (root / "metrics.md").write_text(render_markdown(metrics), encoding="utf-8")
    return root