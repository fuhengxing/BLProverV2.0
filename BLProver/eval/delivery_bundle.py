"""交付包（最终结果）打包：results/<domain>/<theorem>/。

把一个证明成功的定理的最终结果整理成一个清晰的目录，便于交付与统计
（论文 3.2.1 引理来源/线性标签分类；论文 4.1.2 实验指标）：

    results/<domain>/<theorem>/
      README.md                            说明与索引
      index.json                           机器可读清单
      theory/
        defs.thy                           领域定义
        <theorem>.thy                      证明成功的定理（自包含，imports Main）
      lemmas/
        all_lemmas.thy                     全部引理（含证明）
        by_source/<source>_lemmas.thy      按来源（global / middle / repair / unknown）
        by_linear_label/<label>_lemmas.thy 按线性标签（序列不变性 / 操作可执行性 / ...）
      metrics/
        metrics.json                       论文 4.1.2 实验指标（机器可读）
        metrics.md                         论文 4.1.2 实验指标（报告）

交付根目录还汇总全数据集的库级视图（`library/`：引理库总览、生命周期、质量打分与筛选、
分类归档 .thy），以及一份汇总 README（`results/README.md`），按领域/定理列出引理数、
淘汰率与引理库复用率（论文 4.1.2），每次打包自动刷新。

只收录最终产物：中间过程（草图、反思日志、result.json 等）留在运行目录。
"""

from __future__ import annotations

import json
import logging
import re
import shutil
from datetime import datetime
from fnmatch import fnmatch
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Sequence

from ..lemma.domain import normalize_domain, theorem_theory_dir
from .experiment_metrics import metrics_root
from .lemma_library import LIBRARY_FILENAME as LIBRARY_DOC_FILENAME, library_json_path
from .lemma_classification import (
    ALL_LEMMAS_FILENAME,
    INDEX_FILENAME as CLASSIFICATION_INDEX_FILENAME,
    classification_root,
)

logger = logging.getLogger(__name__)

DELIVERY_DIRNAME = "results"
README_FILENAME = "README.md"
DELIVERY_INDEX_FILENAME = "index.json"
FUNNEL_FILENAME = "lemma_funnel.json"
LIBRARY_JSON_FILENAME = "library.json"
RETAINED_LEMMAS_FILENAME = "retained_lemmas.thy"
ELIMINATED_LEMMAS_FILENAME = "eliminated_lemmas.thy"
THEORY_SUBDIR = "theory"
LEMMAS_SUBDIR = "lemmas"
METRICS_SUBDIR = "metrics"
BY_SOURCE_SUBDIR = "by_source"
BY_LINEAR_LABEL_SUBDIR = "by_linear_label"

METRICS_JSON_FILENAME = "metrics.json"
METRICS_MD_FILENAME = "metrics.md"
LIBRARY_SUBDIR = "library"
_LIBRARY_SKIP_GLOBS: Sequence[str] = ("*embeddings*",)

SOURCE_ORDER: Sequence[str] = ("global", "middle", "repair", "unknown")
LINEAR_LABEL_ORDER: Sequence[str] = (
    "sequence_invariance",
    "operation_executability",
    "recursion_termination",
    "order_preservation",
    "nonlinear",
)

_LABEL_ZH: Dict[str, str] = {
    "global": "全局策略引理",
    "middle": "中间引理（依赖非形式化证明）",
    "repair": "修复引理",
    "unknown": "未知来源",
    "sequence_invariance": "序列不变性",
    "operation_executability": "操作可执行性",
    "recursion_termination": "递归终止性",
    "order_preservation": "序关系保持",
    "nonlinear": "非线性（无线性标签）",
}

_LEMMA_NAME_RE = re.compile(
    r"^\s*(?:lemma|corollary|proposition)\s+([A-Za-z0-9_']+)", re.MULTILINE
)
_COMMENTED_LEMMA_RE = re.compile(
    r"^\s*\(\*\s*([A-Za-z0-9_']+)\s*\*\)\s*$", re.MULTILINE
)
_THEOREM_DECL_RE = re.compile(r"^\s*theorem\s+", re.MULTILINE)
_PROOF_START_RE = re.compile(
    r"^\s*(?:proof|by|apply|done|qed|using|unfolding|hence|thus|have|show|"
    r"obtain|from|with|then|moreover|ultimately|also|finally|let|fix|assume|"
    r"presume|note|case|next)\b"
)
_CLASSIFICATION_POINTER_RE = re.compile(
    r"^(\s*index\s*:\s*).*$", re.MULTILINE
)


def delivery_root(
    output_dir: str | Path,
    delivery_dir: Optional[str | Path] = None,
) -> Path:
    """交付包根目录：默认 <output_dir>/results，可用 delivery_dir 覆盖。"""
    if delivery_dir:
        return Path(delivery_dir)
    return Path(output_dir) / DELIVERY_DIRNAME


def bundle_dir(
    output_dir: str | Path,
    domain: str,
    theorem_name: str,
    delivery_dir: Optional[str | Path] = None,
) -> Path:
    """单个定理的交付目录：<root>/<domain>/<theorem>/。"""
    return (
        delivery_root(output_dir, delivery_dir)
        / normalize_domain(domain)
        / (theorem_name or "").strip()
    )


def _reset_dir(path: Path) -> None:
    """Remove an existing bundle directory so a rebuild is idempotent."""
    if path.exists():
        shutil.rmtree(path)


def _copy_file(src: Path, dst: Path) -> bool:
    if not src or not Path(src).is_file():
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    return True


def _read_json(path: Path, default: object) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return default


def _lemma_names_in_thy(text: str) -> List[str]:
    """声明形式的引理名（真正带证明的那些）。"""
    seen: List[str] = []
    for match in _LEMMA_NAME_RE.finditer(text or ""):
        name = match.group(1)
        if name not in seen:
            seen.append(name)
    return seen


def _listed_only_lemma_names(text: str) -> List[str]:
    """只登记、未记录证明的引理名（导出文件里以注释列出）。"""
    seen: List[str] = []
    for match in _COMMENTED_LEMMA_RE.finditer(text or ""):
        name = match.group(1)
        if name not in seen:
            seen.append(name)
    return seen


def _first_theorem_decl(text: str, limit: int = 6) -> str:
    """取 .thy 中的 theorem 声明（不含证明体）。"""
    lines = (text or "").split("\n")
    for idx, line in enumerate(lines):
        if not _THEOREM_DECL_RE.match(line):
            continue
        block = [line.rstrip()]
        for nxt in lines[idx + 1 : idx + limit]:
            if _PROOF_START_RE.match(nxt) or not nxt.strip():
                break
            block.append(nxt.rstrip())
        return "\n".join(block).strip()
    return ""


def _relpath(target: Path, start: Path) -> str:
    try:
        return target.relative_to(start).as_posix()
    except ValueError:
        import os

        return Path(os.path.relpath(str(target), str(start))).as_posix()


def _copy_classification_theories(
    cls_root: Path,
    bundle: Path,
) -> Dict[str, List[str]]:
    """拷贝分类归档 .thy（全部引理 + 按来源 + 按线性标签），并修正文件头索引指针。"""
    copied: Dict[str, List[str]] = {
        "all": [],
        "retained": [],
        "eliminated": [],
        BY_SOURCE_SUBDIR: [],
        BY_LINEAR_LABEL_SUBDIR: [],
    }
    lemmas_root = bundle / LEMMAS_SUBDIR

    def _copy_thy(src: Path, dst: Path) -> bool:
        if not _copy_file(src, dst):
            return False
        try:
            text = dst.read_text(encoding="utf-8")
        except OSError:
            return True
        pointer = _relpath(bundle / DELIVERY_INDEX_FILENAME, dst.parent)
        new_text = _CLASSIFICATION_POINTER_RE.sub(
            lambda m: f"{m.group(1)}{pointer}", text, count=1
        )
        if new_text != text:
            dst.write_text(new_text, encoding="utf-8", newline="\n")
        return True

    all_thy = cls_root / ALL_LEMMAS_FILENAME
    if _copy_thy(all_thy, lemmas_root / ALL_LEMMAS_FILENAME):
        copied["all"] = [ALL_LEMMAS_FILENAME]

    # 论文 4.1.2：生成引理库（all）与留存高质量引理库（retained）分开留档，
    # 便于在最终结果里对比筛选率；被淘汰的引理不丢弃，单独成档。
    for key, filename in (
        ("retained", RETAINED_LEMMAS_FILENAME),
        ("eliminated", ELIMINATED_LEMMAS_FILENAME),
    ):
        if _copy_thy(cls_root / filename, lemmas_root / filename):
            copied[key] = [filename]

    for subdir, bucket in (
        (BY_SOURCE_SUBDIR, BY_SOURCE_SUBDIR),
        (BY_LINEAR_LABEL_SUBDIR, BY_LINEAR_LABEL_SUBDIR),
    ):
        group_root = cls_root / subdir
        if not group_root.is_dir():
            continue
        for thy in sorted(group_root.glob("*/*.thy")):
            rel = f"{subdir}/{thy.name}"
            if _copy_thy(thy, lemmas_root / subdir / thy.name):
                copied[bucket].append(rel)
    return copied


def _render_library_readme() -> str:
    lines: List[str] = []
    lines.append("# 引理库聚合视图（全数据集）")
    lines.append("")
    lines.append(
        "跨定理的库级统计口径；单条定理的交付包见上级目录 `<domain>/<theorem>/`。"
    )
    lines.append("")
    lines.append("| 路径 | 说明 |")
    lines.append("| --- | --- |")
    lines.append(
        "| `proven_lemmas/lemma_library.json` | 引理库总览：逐条引理的陈述、证明、"
        "被调用次数、存活周期、D/U/S/Q（论文 2.4 / 3.1 / 3.2） |"
    )
    lines.append(
        "| `proven_lemmas/lemma_lifecycle.json` | 引理生命周期：首次批次、存活批次、"
        "淘汰批次、Q 历史 |"
    )
    lines.append(
        "| `proven_lemmas/lemma_quality_scores.json` | 最近一批质量打分：S/D/U/Q、"
        "衰减量与是否淘汰 |"
    )
    lines.append(
        "| `proven_lemmas/quality_screening.json` | 最近一批质量筛选结果：淘汰清单、"
        "Qmin 与衰减阈值 |"
    )
    lines.append(
        "| `proven_lemmas/dependency_graph.json` | 引理依赖图：Reach/Edge、"
        "直接调用者与定理引用 |"
    )
    lines.append(
        "| `lemma_classification/index.json` | 每条引理的来源、线性标签、状态与首次定理 |"
    )
    lines.append(
        "| `lemma_classification/all_lemmas.thy` | 生成引理库：过程产出的全部引理"
        "（含已淘汰，含证明） |"
    )
    lines.append(
        "| `lemma_classification/retained_lemmas.thy` | 高质量引理库：质量筛选后留存下来的引理 |"
    )
    lines.append(
        "| `lemma_classification/eliminated_lemmas.thy` | 被筛选淘汰的引理"
        "（留档对比，不丢弃） |"
    )
    lines.append(
        "| `lemma_classification/by_source/*/` | 按来源分类（global / middle / repair / unknown） |"
    )
    lines.append(
        "| `lemma_classification/by_linear_label/*/` | 按线性标签分类（论文 3.2.1） |"
    )
    lines.append("")
    lines.append(
        "- 引理库复用率主口径（论文 4.1.2）= 被**证明成功**定理直接引用的留存引理数"
        " / 留存引理总数；证明失败的定理不计入，也不参与质量评估与筛选。"
    )
    lines.append(
        "- `index.json` 的 status 反映最近一批的打分状态：`in_library` = 本批重新打分通过，"
        "`pending` = 在库但本批未重新打分（仍属留存），`eliminated` = 已淘汰。"
    )
    lines.append("")
    return "\n".join(lines)


def sync_library_view(
    output_dir: str | Path,
    delivery_dir: str | Path,
) -> Optional[Path]:
    """把库级聚合视图拷进交付目录 `<delivery>/library/`（全数据集口径）。

    - `library/proven_lemmas/`        引理库总览（lemma_library.json）、生命周期、
                                      质量打分与筛选、依赖图等 JSON
    - `library/lemma_classification/` 分类归档 .thy（all / retained / eliminated、
                                      by_source、by_linear_label）与 index.json
    """
    out = Path(output_dir)
    dst_root = Path(delivery_dir) / LIBRARY_SUBDIR
    copied = 0
    for name in ("proven_lemmas", "lemma_classification"):
        src = out / "results" / name
        if not src.is_dir():
            continue
        dst = dst_root / name
        _reset_dir(dst)
        for path in sorted(src.rglob("*")):
            if path.is_dir():
                continue
            if any(fnmatch(path.name, pat) for pat in _LIBRARY_SKIP_GLOBS):
                continue
            target = dst / path.relative_to(src)
            if _copy_file(path, target):
                copied += 1
    if not copied:
        return None
    (dst_root / README_FILENAME).write_text(
        _render_library_readme(), encoding="utf-8", newline="\n"
    )
    logger.info("库级聚合视图已同步: %s", dst_root)
    return dst_root


def rebuild_delivery_metrics(
    output_dir: str | Path,
    delivery_dir: str | Path,
    *,
    data_dir: Optional[str | Path] = None,
) -> int:
    """用各交付包自带的快照重算 `metrics/`，不重新证明任何定理。

    每个交付包的指标应反映「该定理成功时」的库状态：引理层取包内 `index.json`
    的快照（`lemma_index`），定理层取该包及之前已生成的定理。重建只在临时目录内
    组装快照后调用 `collect_metrics`，与生产路径共用同一套口径；收尾会同步库级
    聚合视图与交付根 README。
    """
    import tempfile

    from .experiment_metrics import collect_metrics, render_markdown

    out = Path(output_dir)
    root = Path(delivery_dir)
    entries: List[tuple] = []
    for index_file in sorted(root.glob(f"*/*/{DELIVERY_INDEX_FILENAME}")):
        if LIBRARY_SUBDIR in index_file.relative_to(root).parts:
            continue
        data = _read_json(index_file, {})
        if not isinstance(data, dict) or not data.get("lemma_index"):
            continue
        stamp = str(data.get("generated_at") or "")
        if not stamp:
            # 交付包不写实验时间；用 index.json 的落盘时间排序，避免同领域
            # 定理按文件名字母序导致累计指标顺序错乱。
            try:
                stamp = f"{index_file.stat().st_mtime:020.6f}"
            except OSError:
                stamp = ""
        entries.append((stamp, data, index_file.parent))
    entries.sort(key=lambda item: item[0])

    dataset_dir = _resolve_dataset_dir(data_dir, None)
    updated = 0
    with tempfile.TemporaryDirectory(prefix="blprover_metrics_") as tmp:
        for rank, (_ts, data, bundle) in enumerate(entries):
            # 每个交付包用独立临时目录，避免上一个包的 result.json 残留污染本包指标。
            tmp_results = Path(tmp) / f"bundle_{rank}" / "results"
            cls_dir = tmp_results / "lemma_classification"
            cls_dir.mkdir(parents=True, exist_ok=True)
            snapshot: Dict[str, Dict[str, object]] = {}
            for row in data.get("lemma_index") or []:
                if not isinstance(row, Mapping) or not row.get("name"):
                    continue
                item: Dict[str, object] = {
                    "source": row.get("source"),
                    "linear_labels": list(row.get("linear_labels") or []),
                    "status": row.get("status") or "pending",
                    "domain": row.get("domain") or data.get("domain") or "",
                    "first_seen_theorem": row.get("first_seen_theorem") or "",
                }
                # New bundles record has_proof per lemma; keep it so unproven
                # pending lemmas are not counted as retained after a rebuild.
                # Legacy bundles lack the field and fall back to proven names.
                if "has_proof" in row:
                    item["has_proof"] = bool(row.get("has_proof"))
                snapshot[str(row.get("name"))] = item
            (cls_dir / CLASSIFICATION_INDEX_FILENAME).write_text(
                json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
                newline="\n",
            )
            _copy_file(
                bundle / LEMMAS_SUBDIR / ALL_LEMMAS_FILENAME,
                cls_dir / ALL_LEMMAS_FILENAME,
            )
            # 指标按领域累积：不同领域的结果目录同名会互相污染（例如 list
            # 的 mtf_id 混进 sublist 的指标），因此只回放同领域、同领域的定理结果。
            domain = normalize_domain(data.get("domain") or bundle.parent.name)
            for _t, earlier, earlier_bundle in entries[: rank + 1]:
                earlier_domain = normalize_domain(
                    earlier.get("domain") or earlier_bundle.parent.name
                )
                if earlier_domain != domain:
                    continue
                name = str(earlier.get("theorem") or earlier_bundle.name)
                dst = tmp_results / name / "result.json"
                if not _copy_file(out / "results" / name / "result.json", dst):
                    # 历史包可能来自别的 output 目录（result.json 已不在），
                    # 此时用包内 index.json 快照重建一个最小 result.json，
                    # 保证定理层指标与交付时一致，而不是被重建成 0。
                    reuse = (earlier.get("library_summary") or {}).get("reuse") or {}
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    dst.write_text(
                        json.dumps(
                            {
                                "theorem_name": name,
                                "domain": earlier_domain,
                                "status": earlier.get("status") or "",
                                "final_theorem_verified": bool(earlier.get("verified")),
                                "lemma_usage": {
                                    "used_lemma_names": list(
                                        reuse.get("reused_lemma_names") or []
                                    )
                                },
                            },
                            ensure_ascii=False,
                            indent=2,
                        )
                        + "\n",
                        encoding="utf-8",
                        newline="\n",
                    )
            metrics = collect_metrics(
                tmp_results.parent,
                data_dir=_resolve_dataset_dir(
                    dataset_dir, data.get("domain") or bundle.parent.name
                ),
            )
            # 重建在临时目录内计算，不要把临时路径写进交付产物。
            metrics["output_dir"] = str(data.get("output_dir") or "output")
            metrics_dir = bundle / METRICS_SUBDIR
            metrics_dir.mkdir(parents=True, exist_ok=True)
            (metrics_dir / METRICS_JSON_FILENAME).write_text(
                json.dumps(metrics, ensure_ascii=False, indent=2, default=str) + "\n",
                encoding="utf-8",
                newline="\n",
            )
            (metrics_dir / METRICS_MD_FILENAME).write_text(
                render_markdown(metrics), encoding="utf-8", newline="\n"
            )
            updated += 1

    sync_library_view(out, root)
    write_delivery_root_readme(root)
    logger.info("交付指标重建完成: %d 个交付包", updated)
    return updated


def build_delivery_bundle(
    *,
    output_dir: str | Path,
    domain: str,
    theorem_name: str,
    result: Optional[Mapping] = None,
    delivery_dir: Optional[str | Path] = None,
    theorem_data: Optional[Mapping] = None,
    data_dir: Optional[str | Path] = None,
) -> Path:
    """把一个证明成功的定理的最终结果打包到交付目录，返回该目录。"""
    result = dict(result or {})
    bundle = bundle_dir(output_dir, domain, theorem_name, delivery_dir)
    _reset_dir(bundle)
    (bundle / THEORY_SUBDIR).mkdir(parents=True, exist_ok=True)
    (bundle / LEMMAS_SUBDIR).mkdir(parents=True, exist_ok=True)

    theory_dir = theorem_theory_dir(output_dir, domain, theorem_name)
    domain_theory_dir = Path(
        result.get("proven_lemmas_file") or (theory_dir.parent / "proven_lemmas.thy")
    ).parent

    # 1) 证明成功的定理 + 领域定义
    theorem_sources: List[Path] = []
    for candidate in (
        result.get("final_theory_file"),
        Path(output_dir) / "verified" / theorem_name / f"{theorem_name}.thy",
        theory_dir / f"{theorem_name}.thy",
    ):
        if candidate:
            theorem_sources.append(Path(candidate))
    theorem_dst = bundle / THEORY_SUBDIR / f"{theorem_name}.thy"
    theorem_copied = False
    for src in theorem_sources:
        if _copy_file(src, theorem_dst):
            theorem_copied = True
            break
    if not theorem_copied:
        logger.warning("交付包缺少证明成功的定理文件: %s", theorem_sources)

    defs_dst = bundle / THEORY_SUBDIR / "defs.thy"
    defs_copied = _copy_file(domain_theory_dir / "defs.thy", defs_dst)

    # 2) 引理归档（全部 / 按来源 / 按线性标签）
    cls_root = classification_root(output_dir)
    copied_lemmas = _copy_classification_theories(cls_root, bundle)

    # 2b) 引理库总览：陈述 / 证明 / 被调用次数 / 存活周期 / 引理质量
    #     （论文 2.4 / 3.1 / 3.2 / 4.1.2，逐条明细便于快速掌握引理库情况）
    library_dst = bundle / LIBRARY_JSON_FILENAME
    library_doc: Dict[str, object] = {}
    if not _copy_file(library_json_path(output_dir), library_dst):
        try:
            from .lemma_library import build_library_document

            library_doc = build_library_document(
                output_dir,
                domain=normalize_domain(domain),
                theorem_name=theorem_name,
            )
            library_dst.write_text(
                json.dumps(library_doc, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
                newline="\n",
            )
        except Exception as exc:
            logger.warning("引理库总览导出失败: %s", exc)
    if not library_doc:
        loaded = _read_json(library_dst, {})
        library_doc = loaded if isinstance(loaded, dict) else {}

    # 3) 实验指标（论文 4.1.2）
    metrics_src = metrics_root(output_dir)
    metrics_copied: List[str] = []
    for name in (METRICS_JSON_FILENAME, METRICS_MD_FILENAME):
        if _copy_file(metrics_src / name, bundle / METRICS_SUBDIR / name):
            metrics_copied.append(name)
    if not metrics_copied:
        metrics_copied = _write_fresh_metrics(
            output_dir, bundle, data_dir, normalize_domain(domain)
        )

    # 4) 清单 index.json
    cls_index = _read_json(cls_root / CLASSIFICATION_INDEX_FILENAME, {})
    if not isinstance(cls_index, dict):
        cls_index = {}
    all_thy_text = ""
    all_thy_path = bundle / LEMMAS_SUBDIR / ALL_LEMMAS_FILENAME
    if all_thy_path.is_file():
        all_thy_text = all_thy_path.read_text(encoding="utf-8")

    proven_names = _lemma_names_in_thy(all_thy_text)
    listed_names = [
        n for n in _listed_only_lemma_names(all_thy_text) if n not in proven_names
    ]
    lemma_rows: List[Dict[str, object]] = []
    for name in proven_names + listed_names:
        entry = cls_index.get(name)
        entry = dict(entry) if isinstance(entry, dict) else {}
        labels = entry.get("linear_labels") or []
        if isinstance(labels, str):
            labels = [labels]
        lemma_rows.append(
            {
                "name": name,
                "has_proof": name in proven_names,
                "source": str(entry.get("source") or "unknown"),
                "linear_labels": [str(x) for x in labels],
                "status": str(entry.get("status") or ""),
                "domain": str(entry.get("domain") or normalize_domain(domain)),
                "first_seen_theorem": str(entry.get("first_seen_theorem") or ""),
            }
        )

    def _count(key: str) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for row in lemma_rows:
            values = row["linear_labels"] if key == "linear_labels" else [row[key]]
            for value in values or ["unknown"]:
                counts[str(value)] = counts.get(str(value), 0) + 1
        return dict(sorted(counts.items()))

    theorem_text = ""
    if theorem_dst.is_file():
        theorem_text = theorem_dst.read_text(encoding="utf-8")

    funnel = _read_json(
        Path(output_dir) / "results" / theorem_name / FUNNEL_FILENAME, {}
    )
    if not isinstance(funnel, dict) or not funnel:
        funnel = dict(result.get("lemma_funnel") or {})

    index_payload = {
        "domain": normalize_domain(domain),
        "theorem": theorem_name,
        "status": str(result.get("status") or ""),
        "verified": str(result.get("status") or "")
        == "theorem_and_used_lemmas_verified",
        "output_dir": str(output_dir),
        "theory": {
            "theorem": f"{THEORY_SUBDIR}/{theorem_name}.thy" if theorem_copied else "",
            "defs": f"{THEORY_SUBDIR}/defs.thy" if defs_copied else "",
            "theorem_statement_source": "formal theorem statement"
            if theorem_copied
            else "",
        },
        "lemmas": {
            "all": copied_lemmas["all"],
            "retained": copied_lemmas.get("retained") or [],
            "eliminated": copied_lemmas.get("eliminated") or [],
            BY_SOURCE_SUBDIR: copied_lemmas[BY_SOURCE_SUBDIR],
            BY_LINEAR_LABEL_SUBDIR: copied_lemmas[BY_LINEAR_LABEL_SUBDIR],
        },
        "metrics": [f"{METRICS_SUBDIR}/{n}" for n in metrics_copied],
        "library": LIBRARY_JSON_FILENAME if library_dst.is_file() else "",
        "library_summary": library_doc.get("summary") or {},
        "counts": {
            "total": len(lemma_rows),
            "by_source": _count("source"),
            "by_linear_label": _count("linear_labels"),
            "by_status": _count("status"),
        },
        "lemma_funnel": funnel,
        "lemma_index": lemma_rows,
    }
    (bundle / DELIVERY_INDEX_FILENAME).write_text(
        json.dumps(index_payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )

    # 5) README.md
    (bundle / README_FILENAME).write_text(
        _render_readme(
            domain=normalize_domain(domain),
            theorem_name=theorem_name,
            result=result,
            index=index_payload,
            copied_lemmas=copied_lemmas,
            metrics_copied=metrics_copied,
            library=library_doc,
            theorem_text=theorem_text,
        ),
        encoding="utf-8",
        newline="\n",
    )
    delivery = delivery_root(output_dir, delivery_dir)
    try:
        from .domain_library import export_domain_library

        theorem_sources = (
            {theorem_name: theorem_dst} if theorem_dst.is_file() else {}
        )
        export_domain_library(
            output_dir,
            normalize_domain(domain),
            destination=delivery / normalize_domain(domain),
            theorem_sources=theorem_sources,
        )
    except Exception as exc:
        logger.warning("领域级引理库导出失败: %s", exc)
    sync_library_view(output_dir, delivery)
    write_delivery_root_readme(delivery)
    logger.info("交付包已生成: %s", bundle)
    return bundle


def write_delivery_root_readme(delivery_dir: str | Path) -> Path:
    """汇总交付根目录下所有定理的最终结果，写 <delivery_dir>/README.md。"""
    root = Path(delivery_dir)
    root.mkdir(parents=True, exist_ok=True)
    rows: List[Dict[str, object]] = []
    for index_file in sorted(root.glob(f"*/*/{DELIVERY_INDEX_FILENAME}")):
        if LIBRARY_SUBDIR in index_file.relative_to(root).parts:
            # `<delivery>/library/` 是库级聚合视图（自带 index.json），不是定理交付包
            continue
        data = _read_json(index_file, {})
        if not isinstance(data, dict):
            continue
        summary = data.get("library_summary")
        summary = summary if isinstance(summary, dict) else {}
        reuse = summary.get("reuse")
        reuse = reuse if isinstance(reuse, dict) else {}
        counts = data.get("counts")
        counts = counts if isinstance(counts, dict) else {}
        status_counts = counts.get("by_status")
        status_counts = status_counts if isinstance(status_counts, dict) else {}
        verified = bool(data.get("verified"))
        generated_total = summary.get("generated_total")
        if generated_total is None:
            generated_total = counts.get("total") or 0
        library_total = summary.get("library_total")
        if library_total is None:
            library_total = status_counts.get("in_library") or 0
        domain = str(data.get("domain") or index_file.parent.parent.name)
        theorem = str(data.get("theorem") or index_file.parent.name)
        rows.append(
            {
                "domain": domain,
                "theorem": theorem,
                "status_label": "证明成功" if verified else "未通过",
                "status": str(data.get("status") or ""),
                "verified": verified,
                "generated_total": int(generated_total or 0),
                "library_total": int(library_total or 0),
                "eliminated_total": int(summary.get("eliminated_total") or 0),
                "elimination_rate": summary.get("elimination_rate") or 0.0,
                "raw_generated": int((data.get("lemma_funnel") or {}).get("raw_generated") or 0),
                "stage1_count": int((data.get("lemma_funnel") or {}).get("stage1_count") or 0),
                "stage3_count": int((data.get("lemma_funnel") or {}).get("stage3_count") or 0),
                "after_name_filter": int(
                    (data.get("lemma_funnel") or {}).get("after_name_filter") or 0
                ),
                "dedup_names": [
                    d.get("name") or "?"
                    for d in ((data.get("lemma_funnel") or {}).get("dedup_dropped") or [])
                    if isinstance(d, dict)
                ],
                "name_conflict_names": list(
                    (data.get("lemma_funnel") or {}).get("name_conflict_dropped") or []
                ),
                "dedup_dropped": int((data.get("lemma_funnel") or {}).get("dedup_dropped_count") or 0),
                "name_conflict_dropped": int(
                    (data.get("lemma_funnel") or {}).get("name_conflict_dropped_count") or 0
                ),
                "reuse_rate": reuse.get("reuse_rate") or 0.0,
                "reuse_rate_any": reuse.get("reuse_rate_any_reference"),
                "relative_dir": f"{domain}/{theorem}",
            }
        )

    # Legacy bundles predate index.json. Keep them visible in the summary so a
    # new run never hides earlier successful proofs.
    indexed_dirs = {
        f.parent.resolve()
        for f in root.glob(f"*/*/{DELIVERY_INDEX_FILENAME}")
        if LIBRARY_SUBDIR not in f.relative_to(root).parts
    }
    legacy_groups: Dict[str, List[Path]] = {}
    for bundle in sorted(root.glob("*/*")):
        if not bundle.is_dir() or bundle.resolve() in indexed_dirs:
            continue
        if bundle.parent.name == LIBRARY_SUBDIR:
            continue
        theorem = bundle.name
        if not (
            (bundle / f"{theorem}.thy").is_file()
            or (bundle / THEORY_SUBDIR / f"{theorem}.thy").is_file()
        ):
            continue
        legacy_groups.setdefault(bundle.parent.name, []).append(bundle)
    for domain, bundles in sorted(legacy_groups.items()):
        lib_path = root / domain / LIBRARY_JSON_FILENAME
        lib_doc = _read_json(lib_path, {}) if lib_path.is_file() else {}
        lib_sum = lib_doc.get("summary") if isinstance(lib_doc.get("summary"), dict) else {}
        generated = int(lib_sum.get("generated_total") or 0)
        proven = int(lib_sum.get("proven") or 0)
        retained = int(lib_sum.get("retained") or 0)
        eliminated = max(0, proven - retained)
        for rank, bundle in enumerate(bundles):
            first = rank == 0
            rows.append(
                {
                    "domain": domain,
                    "theorem": bundle.name,
                    "status_label": "证明成功",
                    "status": "legacy_delivery",
                    "verified": True,
                    "legacy": True,
                    "generated_total": generated if first else 0,
                    "library_total": retained if first else 0,
                    "eliminated_total": eliminated if first else 0,
                    "elimination_rate": (
                        round(eliminated / generated, 4) if generated and first else 0.0
                    ),
                    "raw_generated": 0,
                    "stage1_count": 0,
                    "stage3_count": 0,
                    "after_name_filter": 0,
                    "dedup_names": [],
                    "name_conflict_names": [],
                    "dedup_dropped": 0,
                    "name_conflict_dropped": 0,
                    "reuse_rate": 0.0,
                    "reuse_rate_any": None,
                    "relative_dir": f"{domain}/{bundle.name}",
                }
            )

    verified_rows = [r for r in rows if r["verified"]]
    domains = sorted({str(r["domain"]) for r in rows})
    raw_sum = sum(int(r["raw_generated"]) for r in rows)
    dedup_sum = sum(int(r["dedup_dropped"]) for r in rows)
    name_sum = sum(int(r["name_conflict_dropped"]) for r in rows)
    generated_sum = sum(int(r["generated_total"]) for r in rows)
    library_sum = sum(int(r["library_total"]) for r in rows)
    eliminated_sum = sum(int(r["eliminated_total"]) for r in rows)
    reuse_any_values = [
        float(r["reuse_rate_any"]) for r in rows if r["reuse_rate_any"] is not None
    ]
    reuse_rows = [r for r in verified_rows if not r.get("legacy")]
    main_rate = (
        round(sum(float(r["reuse_rate"]) for r in reuse_rows) / len(reuse_rows), 4)
        if reuse_rows
        else 0.0
    )
    any_rate = (
        round(sum(reuse_any_values) / len(reuse_any_values), 4)
        if reuse_any_values
        else 0.0
    )

    lines: List[str] = []
    lines.append("# BLProver 交付结果汇总")
    lines.append("")
    lines.append(f"- 交付根目录：`{root}`")
    lines.append(
        f"- 领域 {len(domains)} 个 ｜ 定理 {len(rows)} 条 ｜ 证明成功 {len(verified_rows)} 条"
    )
    lines.append("")
    lines.append("## 汇总指标（各交付包快照合计）")
    lines.append("")
    lines.append("| 指标 | 数值 | 说明 |")
    lines.append("| --- | --- | --- |")
    lines.append(
        f"| 定理成功率 | {round(len(verified_rows) / len(rows), 4) if rows else 0.0} | "
        f"{len(verified_rows)} / {len(rows)}（内核校验通过） |"
    )
    lines.append(f"| 生成引理总数 | {generated_sum} | 各交付包合计（含已淘汰） |")
    lines.append(f"| 高质量引理库存活 | {library_sum} | 质量筛选后留存 |")
    lines.append(f"| 被淘汰引理 | {eliminated_sum} | 留档 eliminated_lemmas.thy |")
    lines.append(
        f"| 素材漏斗（模型原始生成 → 本批去重 → 剔除引理库同名） | "
        f"{raw_sum} → {raw_sum - dedup_sum} → {raw_sum - dedup_sum - name_sum} | "
        "本批去重丢弃 %d，引理库同名丢弃 %d（各交付包合计） |"
        % (dedup_sum, name_sum)
    )
    lines.append(
        f"| 淘汰率 | {round(eliminated_sum / generated_sum, 4) if generated_sum else 0.0} | "
        "淘汰引理 / 生成引理 |"
    )
    lines.append(
        f"| 引理库复用率（主口径：仅定理引用） | {main_rate} | "
        "被证明成功定理引用的留存引理 / 留存引理（已证明成功的交付包均值） |"
    )
    lines.append(
        f"| 副口径复用率（含库内引理互相调用） | {any_rate} | 仅作对比，不作论文口径 |"
    )
    lines.append("")
    lines.append("## 生成漏斗明细（模型原始生成 → 本批去重 → 剔除引理库同名）")
    lines.append("")
    lines.append("| 领域 | 定理 | step1 全局 | step3 中间 | 原始 | 去重丢弃 | 同名丢弃 | 最终候选 | 去重丢弃名单 | 同名丢弃名单 |")
    lines.append("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in rows:
        lines.append(
            f"| {r['domain']} | {r['theorem']} | {r['stage1_count']} | {r['stage3_count']} | "
            f"{r['raw_generated']} | {r['dedup_dropped']} | {r['name_conflict_dropped']} | "
            f"{r['after_name_filter']} | {', '.join(r['dedup_names']) or '-'} | "
            f"{', '.join(r['name_conflict_names']) or '-'} |"
        )
    lines.append("")
    lines.append("## 明细")
    lines.append("")
    lines.append(
        "| 领域 | 定理 | 状态 | 生成引理 | 留存 | 淘汰 | 淘汰率 | 复用率(主) | 复用率(副) | 交付目录 |"
    )
    lines.append("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in rows:
        row_any = r["reuse_rate_any"]
        lines.append(
            f"| {r['domain']} | {r['theorem']} | {r['status_label']} | "
            f"{r['generated_total']} | {r['library_total']} | {r['eliminated_total']} | "
            f"{r['elimination_rate']} | {r['reuse_rate']} | "
            f"{row_any if row_any is not None else '-'} | `{r['relative_dir']}/` |"
        )
    lines.append("")
    lines.append("## 说明")
    lines.append("")
    lines.append(
        "- 每条定理的交付包结构见对应目录下的 `README.md`；逐条引理明细（陈述、证明、"
        "被调用次数、存活周期、D/U/S/Q）见各包内 `library.json`。"
    )
    lines.append(
        "- 引理库复用率主口径 = 被**证明成功**定理直接引用的留存引理数 / 留存引理总数；"
        "证明失败的定理不计入，也不参与质量评估与筛选。"
    )
    lines.append(
        "- 汇总表按交付包累加：同一引理若被多个定理的交付包同时收录会在合计里重复计数，"
        "跨定理的库级统计请以 `library/proven_lemmas/lemma_library.json` 为准。"
    )
    lines.append(
        "- `library/` 是全数据集的库级聚合视图（引理库总览、生命周期、质量打分与筛选、"
        "分类归档 .thy），详见 `library/README.md`。"
    )
    lines.append("")

    lib_doc = _read_json(
        root / LIBRARY_SUBDIR / "proven_lemmas" / LIBRARY_DOC_FILENAME, {}
    )
    lib_summary = lib_doc.get("summary") if isinstance(lib_doc, Mapping) else None
    if isinstance(lib_summary, Mapping) and lib_summary:
        lib_reuse = lib_summary.get("reuse") or {}
        lines.append("## 库级去重汇总（跨定理，论文 4.1.2 主口径）")
        lines.append("")
        lines.append("| 指标 | 数值 | 说明 |")
        lines.append("| --- | --- | --- |")
        lines.append(
            f"| 候选引理（库级去重） | {lib_summary.get('registered_total', 0)} | "
            "登记引理总数（含仅登记未证的引理） |"
        )
        lines.append(
            f"| 生成引理（库级去重） | {lib_summary.get('generated_total', 0)} | 已证明引理 |"
        )
        lines.append(
            f"| 留存引理（库级去重） | {lib_summary.get('library_total', 0)} | 质量筛选后仍在库 |"
        )
        lines.append(
            f"| 淘汰引理（库级去重） | {lib_summary.get('eliminated_total', 0)} | "
            "留档 `library/lemma_classification/eliminated_lemmas.thy` |"
        )
        lines.append(
            f"| 淘汰率（库级去重） | {lib_summary.get('elimination_rate', 0.0)} | 淘汰 / 候选 |"
        )
        lines.append(
            f"| 引理库复用率（库级去重，主口径：仅定理引用） | "
            f"{lib_reuse.get('reuse_rate', 0.0)} | 被成功定理引用的留存引理 / 留存引理 |"
        )
        lines.append("")
        lines.append(
            "- 本表为跨定理去重后的库级口径，数据源 `library/proven_lemmas/lemma_library.json`；"
            "上方「汇总指标」是各交付包快照的合计，同一引理会被重复计数。"
        )
        lines.append("")

    # Keep dataset provenance visible in the auto-generated summary.
    project_root = Path(__file__).resolve().parents[2]
    sources = [
        ("boundedstack", "\u6709\u754c\u6808", "\u9879\u76ee\u81ea\u5e26\u6570\u636e\u96c6"),
        ("sublist", "\u5b50\u5217\u8868", "\u9879\u76ee\u81ea\u5e26\u6570\u636e\u96c6"),
        (
            "list",
            "\u81ea\u7ec4\u7ec7\u5217\u8868\uff08move-to-front / "
            "\u5728\u7ebf\u7b97\u6cd5\u7ade\u4e89\u5206\u6790\uff09",
            "AFP List_Update\uff08Tobias Nipkow\uff09",
        ),
    ]
    lines.append("## \u6570\u636e\u96c6\u6765\u6e90")
    lines.append("")
    lines.append("| \u9886\u57df | \u6570\u636e\u96c6 | \u6765\u6e90 | \u5b9a\u7406\u6570 |")
    lines.append("| --- | --- | --- | --- |")
    for dom, desc, src in sources:
        dom_dir = project_root / "data" / dom
        count = len(list(dom_dir.glob("*.json"))) if dom_dir.is_dir() else 0
        lines.append(f"| `{dom}` | {desc} | {src} | {count} |")
    lines.append("")
    lines.append(
        "- `list` \u6765\u81ea AFP `List_Update`\uff08Tobias Nipkow\uff09\uff0c"
        "\u9010\u6761\u6765\u6e90\u4e0e\u884c\u53f7\u89c1 `data/list/SOURCES.md`\u3002"
    )
    lines.append("")

    path = root / README_FILENAME
    path.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    return path


def _resolve_dataset_dir(
    data_dir: Optional[str | Path],
    domain: Optional[str],
) -> Optional[Path]:
    """Point dataset counting at the domain subdirectory when it exists."""
    if not data_dir:
        return None
    root = Path(data_dir)
    if domain:
        candidate = root / normalize_domain(domain)
        if candidate.is_dir():
            return candidate
    return root


def _write_fresh_metrics(
    output_dir: str | Path,
    bundle: Path,
    data_dir: Optional[str | Path],
    domain: Optional[str] = None,
) -> List[str]:
    """运行目录还没有论文 4.1.2 指标报告时，现场汇总一份写进交付包。"""
    try:
        from .experiment_metrics import collect_metrics, render_markdown

        metrics = collect_metrics(
            output_dir, data_dir=_resolve_dataset_dir(data_dir, domain)
        )
        metrics_dir = bundle / METRICS_SUBDIR
        metrics_dir.mkdir(parents=True, exist_ok=True)
        (metrics_dir / METRICS_JSON_FILENAME).write_text(
            json.dumps(metrics, ensure_ascii=False, indent=2, default=str) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        (metrics_dir / METRICS_MD_FILENAME).write_text(
            render_markdown(metrics), encoding="utf-8", newline="\n"
        )
        return [METRICS_JSON_FILENAME, METRICS_MD_FILENAME]
    except Exception as exc:
        logger.warning("交付包指标生成失败: %s", exc)
        return []


def _render_readme(
    *,
    domain: str,
    theorem_name: str,
    result: Mapping,
    index: Mapping,
    copied_lemmas: Mapping[str, List[str]],
    metrics_copied: Sequence[str],
    theorem_text: str,
    library: Optional[Mapping] = None,
) -> str:
    counts = index.get("counts") or {}
    by_source = counts.get("by_source") or {}
    by_label = counts.get("by_linear_label") or {}
    by_status = counts.get("by_status") or {}
    status = str(result.get("status") or "")
    verified = bool(index.get("verified"))
    decl = _first_theorem_decl(theorem_text)

    lines: List[str] = []
    lines.append(f"# {domain} / {theorem_name}")
    lines.append("")
    lines.append(f"- 领域：`{domain}`")
    lines.append(f"- 定理：`{theorem_name}`")
    lines.append(
        "- 状态："
        + ("证明成功（定理与被引用引理均已通过 Isabelle 校验）" if verified else status)
    )
    outer = result.get("theorem_outer_attempts")
    if outer:
        lines.append(f"- 外层尝试次数：{outer}")
    lines.append("")
    lines.append("## 目录结构")
    lines.append("")
    lines.append("| 路径 | 说明 |")
    lines.append("| --- | --- |")
    lines.append(
        f"| `theory/{theorem_name}.thy` | 证明成功的定理（自包含，`imports Main`，可直接用 Isabelle 打开） |"
    )
    lines.append("| `theory/defs.thy` | 领域定义（该数据结构的类型与函数定义） |")
    lines.append("| `lemmas/all_lemmas.thy` | 生成引理库：过程产出的全部引理（含已淘汰，含证明） |")
    lines.append("| `lemmas/retained_lemmas.thy` | 高质量引理库：质量筛选后留存下来的引理 |")
    lines.append("| `lemmas/eliminated_lemmas.thy` | 被筛选淘汰的引理（留档对比，不丢弃） |")
    lines.append("| `lemmas/by_source/*.thy` | 按来源分类的引理（global / middle / repair） |")
    lines.append("| `lemmas/by_linear_label/*.thy` | 按线性标签分类的引理（论文 3.2.1） |")
    lines.append("| `metrics/metrics.json`、`metrics/metrics.md` | 实验指标（论文 4.1.2） |")
    lines.append(
        "| `library.json` | 引理库总览：逐条引理的陈述、证明、被调用次数、存活周期、"
        "质量（论文 2.4 / 3.1 / 3.2） |"
    )
    lines.append("| `index.json` | 机器可读清单（定理状态 + 每条引理的来源/线性标签/状态） |")
    lines.append("")
    if decl:
        lines.append("## 定理陈述")
        lines.append("")
        lines.append("```isabelle")
        lines.append(decl)
        lines.append("```")
        lines.append("")
    lines.append("## 引理统计（论文 3.2.1）")
    lines.append("")
    lines.append(f"- 引理总数：**{counts.get('total', 0)}**")
    lines.append("")
    lines.append("| 来源 | 标签含义 | 数量 |")
    lines.append("| --- | --- | --- |")
    for key in list(SOURCE_ORDER) + [k for k in by_source if k not in SOURCE_ORDER]:
        lines.append(
            f"| `{key}` | {_LABEL_ZH.get(key, '-')} | {by_source.get(key, 0)} |"
        )
    lines.append("")
    lines.append("| 线性标签 | 标签含义 | 数量 |")
    lines.append("| --- | --- | --- |")
    for key in list(LINEAR_LABEL_ORDER) + [k for k in by_label if k not in LINEAR_LABEL_ORDER]:
        lines.append(
            f"| `{key}` | {_LABEL_ZH.get(key, '-')} | {by_label.get(key, 0)} |"
        )
    lines.append("")
    if by_status:
        lines.append("- 引理状态：" + "，".join(f"{k} {v} 条" for k, v in by_status.items()))
        lines.append("")
    lemma_index = index.get("lemma_index") or []
    if lemma_index:
        lines.append("## 引理清单")
        lines.append("")
        lines.append("| 引理 | 来源 | 线性标签 | 状态 | 证明 |")
        lines.append("| --- | --- | --- | --- | --- |")
        for row in lemma_index:
            labels = "、".join(row.get("linear_labels") or []) or "-"
            proof = "有" if row.get("has_proof") else "无（仅登记）"
            lines.append(
                f"| `{row.get('name')}` | {row.get('source')} | {labels} | "
                f"{row.get('status') or '-'} | {proof} |"
            )
        lines.append("")
    lib = dict(library or {})
    lib_summary = lib.get("summary") or {}
    if lib_summary:
        reuse = lib_summary.get("reuse") or {}
        quality = lib_summary.get("quality") or {}
        lines.append("## 引理库总览与筛选对比（论文 4.1.2）")
        lines.append("")
        lines.append("| 引理库视图 | 引理数 | 文件 |")
        lines.append("| --- | --- | --- |")
        lines.append(
            f"| 生成引理库（全部已证明） | {lib_summary.get('generated_total', 0)} | "
            "`lemmas/all_lemmas.thy` |"
        )
        lines.append(
            f"| 高质量引理库（留存） | {lib_summary.get('library_total', 0)} | "
            "`lemmas/retained_lemmas.thy` |"
        )
        lines.append(
            f"| 被淘汰引理 | {lib_summary.get('eliminated_total', 0)} | "
            "`lemmas/eliminated_lemmas.thy` |"
        )
        lines.append("")
        lines.append(
            f"- 留存引理 **{lib_summary.get('library_total', 0)}** 条，"
            f"淘汰 {lib_summary.get('eliminated_total', 0)} 条，"
            f"淘汰率 **{lib_summary.get('elimination_rate', 0.0)}**"
        )
        lines.append(
            f"- 引理库复用率（论文 4.1.2 主口径：仅定理引用）："
            f"**{reuse.get('reuse_rate', 0.0)}**"
            f"（被定理引用的留存引理 {reuse.get('referenced_library_lemmas', 0)} 条"
            f" / 留存引理 {reuse.get('library_lemmas', 0)} 条）"
        )
        if reuse.get("reuse_rate_any_reference") is not None:
            lines.append(
                f"- 副口径复用率（含库内引理互相调用）："
                f"**{reuse.get('reuse_rate_any_reference', 0.0)}**"
                f"（{reuse.get('referenced_library_lemmas_any', 0)} 条）"
            )
        lines.append(
            f"- 被调用总次数：{lib_summary.get('call_count_total', 0)}；"
            f"引理质量 Q(i)：均值 {quality.get('mean')}，"
            f"最大 {quality.get('max')}，最小 {quality.get('min')}"
        )
        lines.append("")
        lines.append(
            "- 逐条明细（陈述、形式化证明、被调用次数、存活周期、D/U/S/Q 与衰减）"
            "见 `library.json`。"
        )
        lines.append("")
    if metrics_copied:
        lines.append("## 实验指标（论文 4.1.2）")
        lines.append("")
        lines.append("见 `metrics/metrics.json`（机器可读）与 `metrics/metrics.md`（报告）。")
        lines.append("")
    lines.append("## 如何查看")
    lines.append("")
    lines.append(
        f"1. 用 Isabelle/jEdit 打开 `theory/{theorem_name}.thy`：定理自包含，"
        "无 `sorry` / `sledgehammer` 占位。"
    )
    lines.append("2. 用 Isabelle/jEdit 打开 `lemmas/all_lemmas.thy`：查看全部引理及其证明。")
    lines.append("3. 用 `index.json` 做后续统计：按来源（global / middle / repair）与线性标签分别汇总。")
    lines.append(
        "4. 用 `library.json` 了解引理库总体情况：逐条引理的陈述、证明、被调用次数、"
        "存活周期与引理质量。"
    )
    lines.append("")
    return "\n".join(lines)
