"""领域级引理库导出（论文 2.4 / 3.2.1 / 4.1.2）。

每个线性数据结构领域一个目录，目录内集中存放可共享的库文件：

    <destination>/
      defs.thy                    领域全部函数定义（累积、不覆盖）
      proven_lemmas.thy           所有证明成功的引理（含后续被质量筛选淘汰者）
      all_constructed_lemmas.thy  该领域生成过的全部引理（含未证明，以 sorry 留档）
      excellent_lemmas.thy        质量筛选后留存的引理
      lemmas1.thy                 阶段 1：全局引理生成
      lemmas2.thy                 阶段 2：中间引理提取
      lemmas3.thy                 阶段 3：修复引理构造
      linear_<label>_lemmas.thy    按线性标签归档（论文 3.2.1，四类 + 非线性）
      lemma_stage_classification.csv
      library.json                逐条引理元数据（来源/阶段/质量/状态）
      readme.txt
      <theorem>/<theorem>.thy     单定理产物（与库文件同层）

定理目录只保留定理自身；引理库、定义与来源统计全部上移到领域级，便于跨定理共享。
"""

from __future__ import annotations

import csv
import json
import re
import shutil
import tempfile
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from ..lemma.definition_store import DefinitionStore
from ..lemma.domain import get_domain_group, normalize_domain, theorem_theory_dir
from ..lemma.proven_lemma_store import ProvenLemmaStore
from ..lemma.thy_imports import DEFS_THEORY_NAME, PROVEN_THEORY_NAME
from .lemma_library import split_statement_proof

LIBRARY_DIRNAME = "proven_lemmas"
LIBRARY_JSON_FILENAME = "lemma_library.json"
LIBRARY_LABELS_FILENAME = "lemma_labels.json"
DOMAIN_LIBRARY_JSON = "library.json"
DOMAIN_README = "readme.txt"
STAGE_CSV = "lemma_stage_classification.csv"

STAGE_FILE = {
    "global": "lemmas1",
    "middle": "lemmas2",
    "repair": "lemmas3",
}
STAGE_LABEL = {
    "global": "阶段1",
    "middle": "阶段2",
    "repair": "阶段3",
}

LINEAR_LABEL_PREFIX = "linear_"
LINEAR_LABEL_SUFFIX = "_lemmas"
LINEAR_LABEL_ORDER: Sequence[str] = (
    "sequence_invariance",
    "operation_executability",
    "recursion_termination",
    "order_preservation",
    "nonlinear",
)
def linear_label_theory(label: str) -> str:
    return f"{LINEAR_LABEL_PREFIX}{label}{LINEAR_LABEL_SUFFIX}"


LINEAR_LABEL_ZH: Dict[str, str] = {
    "sequence_invariance": "序列不变性",
    "operation_executability": "操作可执行性",
    "recursion_termination": "递归终止性",
    "order_preservation": "序关系保持",
    "nonlinear": "非线性（无线性标签）",
}

_FACT_NAME_RE = re.compile(r"^\s*(?:lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_']+)", re.MULTILINE)


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


def domain_dir_for(output_dir: str | Path, domain: str) -> Path:
    return Path(output_dir) / "results" / normalize_domain(domain)


def load_library_rows(output_dir: str | Path, domain: str = "") -> List[dict]:
    """读取当前输出目录的逐条引理元数据。"""
    root = Path(output_dir) / "results" / LIBRARY_DIRNAME
    payload = _load_json(root / LIBRARY_JSON_FILENAME, {})
    rows = payload.get("lemmas") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        return []
    out = [dict(r) for r in rows if isinstance(r, dict) and r.get("name")]
    if domain:
        d = normalize_domain(domain)
        out = [r for r in out if not r.get("domain") or str(r["domain"]) == d]
        # Pending lemmas have metadata but no statement/proof in lemma_library.json.
        # Hydrate them from the unproven index so they can be archived with `sorry`.
        index = _load_json(root / f"unproven_lemmas_index_{d}.json", {})
        unproven = index.get("lemmas") if isinstance(index, dict) else None
        if isinstance(unproven, dict):
            from ..lemma.proven_lemma_store import ProvenLemmaStore
            from ..lemma.unproven_lemma_store import strip_lemma_proof_body

            for row in out:
                if str(row.get("statement") or "").strip():
                    continue
                rec = unproven.get(str(row.get("name") or ""))
                if not isinstance(rec, dict):
                    continue
                stmt = strip_lemma_proof_body(str(rec.get("statement") or ""))
                stmt = ProvenLemmaStore._sanitize_isabelle_symbols(stmt)
                stmt = re.sub(r"\n\s*sorry\s*$", "", stmt).rstrip()
                if stmt:
                    row["statement"] = stmt
                    row.setdefault("stage", rec.get("stage"))
    return out


def merge_library_rows(documents: Iterable[Mapping[str, object]]) -> List[dict]:
    """合并多次运行的引理元数据；同名优先保留“有证明 + 质量更高”的记录。"""
    merged: Dict[str, dict] = {}
    for document in documents:
        rows = document.get("lemmas") if isinstance(document, Mapping) else None
        if not isinstance(rows, list):
            continue
        for raw in rows:
            if not isinstance(raw, Mapping):
                continue
            name = str(raw.get("name") or "")
            if not name:
                continue
            row = dict(raw)
            old = merged.get(name)
            if old is None:
                merged[name] = row
                continue
            old_proof = bool(old.get("has_proof"))
            new_proof = bool(row.get("has_proof"))
            if new_proof and not old_proof:
                merged[name] = row
                continue
            if new_proof == old_proof:
                old_q = (old.get("quality") or {}).get("q")
                new_q = (row.get("quality") or {}).get("q")
                try:
                    if new_q is not None and (old_q is None or float(new_q) > float(old_q)):
                        merged[name] = row
                except (TypeError, ValueError):
                    pass
    rows = list(merged.values())
    rows.sort(key=lambda r: (0 if r.get("has_proof") else 1, str(r.get("name") or "")))
    for idx, row in enumerate(rows, start=1):
        row["id"] = idx
    return rows


def _row_block(row: Mapping[str, object], *, allow_sorry: bool) -> str:
    statement = str(row.get("statement") or "").strip()
    proof = str(row.get("proof") or "").strip()
    if not statement:
        return ""
    if proof:
        return f"{statement}\n{proof}".rstrip()
    if allow_sorry:
        return f"{statement}\n  sorry"
    return ""


def _referenced_names(text: str, candidates: Iterable[str]) -> set[str]:
    refs: set[str] = set()
    for name in candidates:
        if not name:
            continue
        if re.search(r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])", text or ""):
            refs.add(name)
    return refs


def _ordered_names(rows: Sequence[Mapping[str, object]]) -> List[str]:
    """按证明依赖排序；无依赖的按 id/名称稳定排序。"""
    by_name = {str(r.get("name")): r for r in rows}
    names = [str(r.get("name")) for r in rows]
    deps: Dict[str, set[str]] = {}
    for name in names:
        row = by_name[name]
        body = f"{row.get('statement') or ''}\n{row.get('proof') or ''}"
        deps[name] = _referenced_names(body, [n for n in names if n != name])
    placed: List[str] = []
    placed_set: set[str] = set()
    while len(placed) < len(names):
        ready = [n for n in names if n not in placed_set and deps[n] <= placed_set]
        if not ready:
            ready = [n for n in names if n not in placed_set]
        ready.sort(key=lambda n: (int(by_name[n].get("id") or 10 ** 6), n))
        nxt = ready[0]
        placed.append(nxt)
        placed_set.add(nxt)
    return placed


def _render_library_thy(
    theory_name: str,
    *,
    imports: str,
    rows: Sequence[Mapping[str, object]],
    header: str = "",
    allow_sorry: bool = True,
    dependency_rows: Sequence[Mapping[str, object]] = (),
) -> str:
    lines: List[str] = [f'theory "{theory_name}"', f"imports {imports}", "begin", ""]
    if allow_sorry:
        lines.append("declare [[quick_and_dirty = true]]")
        lines.append("")
    if header:
        lines.extend([f"(* {header} *)", ""])
    dep_names = {str(r.get("name")) for r in dependency_rows}
    for name in _ordered_names(list(rows)):
        row = next(r for r in rows if str(r.get("name")) == name)
        block = _row_block(row, allow_sorry=allow_sorry)
        if not block:
            continue
        status = "dependency" if name in dep_names else str(row.get("status") or "")
        if status:
            lines.append(f"(* ==== {name} ({status}) ==== *)")
        lines.append(block)
        lines.append("")
    lines.append("end")
    lines.append("")
    return "\n".join(lines)


def _merge_defs_from_data(data_dir: str | Path, domain: str) -> str:
    """用临时目录把领域全部数据文件的定义合并成一份完整 defs 文本。"""
    with tempfile.TemporaryDirectory(prefix="blprover_defs_") as tmp:
        DefinitionStore.merge_from_domain_data(tmp, domain, data_dir)
        path = DefinitionStore.defs_thy_path(tmp, domain)
        if not path.is_file():
            return ""
        return path.read_text(encoding="utf-8")


def _read_proven_thy(output_dir: str | Path, domain: str) -> str:
    path = ProvenLemmaStore.proven_thy_path(output_dir, domain)
    if path.is_file():
        return path.read_text(encoding="utf-8")
    return ""


def _collect_proven_blocks(output_dirs: Iterable[str | Path], domain: str) -> Dict[str, str]:
    from .proof_difficulty_score_v2.thy_extract import extract_decl_blocks

    blocks: Dict[str, str] = {}
    for output_dir in output_dirs:
        text = _read_proven_thy(output_dir, domain)
        if not text:
            continue
        for name, block in extract_decl_blocks(text).items():
            if name:
                blocks.setdefault(name, block)
    return blocks


def _render_proven_thy(blocks: Mapping[str, str]) -> str:
    rows = []
    for name, block in blocks.items():
        parts = split_statement_proof(block)
        rows.append(
            {
                "name": name,
                "statement": parts["statement"],
                "proof": parts["proof"],
                "has_proof": bool(parts["proof"]),
                "id": 0,
            }
        )
    # 引理之间可能有依赖，先按名称出现顺序排，再用拓扑排序
    for idx, row in enumerate(rows, start=1):
        row["id"] = idx
    return _render_library_thy(
        PROVEN_THEORY_NAME,
        imports=f"Main {DEFS_THEORY_NAME}",
        rows=rows,
        header="领域已证明引理库（跨定理共享）",
        allow_sorry=False,
    )


def _row_linear_labels(row: Mapping[str, object]) -> List[str]:
    """取一条引理的线性标签；无标签视为 nonlinear（与质量筛选口径一致）。"""
    labels = row.get("linear_labels")
    if isinstance(labels, str):
        labels = [labels]
    values = [str(x).strip() for x in (labels or []) if str(x).strip()]
    return values or ["nonlinear"]


def _augment_proven_blocks(
    blocks: Mapping[str, str],
    rows: Sequence[Mapping[str, object]],
) -> Dict[str, str]:
    """把库内记录中“已证明但不在 proven 文件里”的引理补回（含已被淘汰者）。"""
    merged = dict(blocks)
    for row in rows:
        name = str(row.get("name") or "")
        if not name or name in merged or not bool(row.get("has_proof")):
            continue
        block = _row_block(row, allow_sorry=False)
        if block:
            merged[name] = block
    return merged


def _with_dependency_closure(
    rows: Sequence[Mapping[str, object]],
    seed_names: Iterable[str],
) -> List[Mapping[str, object]]:
    """在给定引理集合内做依赖闭包；只接收已证明且未淘汰的候选集合。"""
    by_name = {str(r.get("name") or ""): r for r in rows}
    wanted = {str(n) for n in seed_names if str(n) in by_name}
    changed = True
    while changed:
        changed = False
        for name in list(wanted):
            row = by_name.get(name) or {}
            body = f"{row.get('statement') or ''}\n{row.get('proof') or ''}"
            for dep in _referenced_names(body, set(by_name) - {name}):
                if dep not in wanted:
                    wanted.add(dep)
                    changed = True
    return [row for row in rows if str(row.get("name") or "") in wanted]


def _count_linear_labels(rows: Sequence[Mapping[str, object]]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for row in rows:
        for label in _row_linear_labels(row):
            counts[label] = counts.get(label, 0) + 1
    return dict(sorted(counts.items()))


def _copy_theorem_outputs(
    destination: Path,
    *,
    theorem_sources: Mapping[str, Path],
) -> List[str]:
    copied: List[str] = []
    for theorem, source in sorted(theorem_sources.items()):
        if not theorem or not source or not Path(source).is_file():
            continue
        target_dir = destination / theorem
        target_dir.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target_dir / f"{theorem}.thy")
        summary = Path(source).parent / "proof_summary.md"
        if summary.is_file():
            shutil.copyfile(summary, target_dir / "proof_summary.md")
        copied.append(theorem)
    return copied


def export_domain_library(
    output_dir: str | Path,
    domain: str,
    *,
    destination: Optional[str | Path] = None,
    theorem_names: Optional[Sequence[str]] = None,
    data_dir: Optional[str | Path] = None,
    theorem_sources: Optional[Mapping[str, Path]] = None,
    defs_text: Optional[str] = None,
    proven_blocks: Optional[Mapping[str, str]] = None,
    rows: Optional[Sequence[Mapping[str, object]]] = None,
) -> Path:
    """把一个领域的引理库导出为领域级目录（默认 <output>/results/<domain>）。"""
    domain = normalize_domain(domain)
    destination = Path(destination) if destination else domain_dir_for(output_dir, domain)
    destination.mkdir(parents=True, exist_ok=True)

    if defs_text is None:
        defs_path = DefinitionStore.defs_thy_path(output_dir, domain)
        if defs_path.is_file():
            defs_text = defs_path.read_text(encoding="utf-8")
        elif data_dir:
            defs_text = _merge_defs_from_data(data_dir, domain)
        else:
            defs_text = ""
    if defs_text.strip():
        (destination / f"{DEFS_THEORY_NAME}.thy").write_text(
            defs_text.rstrip() + "\n", encoding="utf-8", newline="\n"
        )

    if rows is None:
        rows = load_library_rows(output_dir, domain)
        # 领域库是跨定理共享的：output 被清理或换目录后，本轮引理不能覆盖
        # 目标目录里已有的历史引理，否则早期定理的生成引理会整批丢失。
        existing = _load_json(destination / DOMAIN_LIBRARY_JSON, {})
        old_rows = existing.get("lemmas") if isinstance(existing, dict) else None
        if isinstance(old_rows, list) and old_rows:
            rows = merge_library_rows([{"lemmas": rows}, {"lemmas": old_rows}])
    rows = list(rows)

    if proven_blocks is None:
        proven_text = _read_proven_thy(output_dir, domain)
        proven_blocks = _collect_proven_blocks([output_dir], domain)
        merged_blocks = _augment_proven_blocks(proven_blocks, rows)
        if merged_blocks != dict(proven_blocks):
            (destination / f"{PROVEN_THEORY_NAME}.thy").write_text(
                _render_proven_thy(merged_blocks), encoding="utf-8", newline="\n"
            )
        elif proven_text:
            (destination / f"{PROVEN_THEORY_NAME}.thy").write_text(
                proven_text.rstrip() + "\n", encoding="utf-8", newline="\n"
            )
        proven_blocks = merged_blocks
    else:
        merged_blocks = _augment_proven_blocks(proven_blocks, rows)
        (destination / f"{PROVEN_THEORY_NAME}.thy").write_text(
            _render_proven_thy(merged_blocks), encoding="utf-8", newline="\n"
        )
        proven_blocks = merged_blocks

    all_blocks = [r for r in rows if str(r.get("statement") or "").strip()]
    (destination / "all_constructed_lemmas.thy").write_text(
        _render_library_thy(
            "all_constructed_lemmas",
            imports=f"Main {DEFS_THEORY_NAME}",
            rows=all_blocks,
            header="该领域生成过的全部引理（未证明者以 sorry 留档，仅供对比）",
            allow_sorry=True,
        ),
        encoding="utf-8",
        newline="\n",
    )

    excellent = [
        r for r in rows
        if str(r.get("status") or "") != "eliminated" and bool(r.get("has_proof"))
    ]
    (destination / "excellent_lemmas.thy").write_text(
        _render_library_thy(
            "excellent_lemmas",
            imports=f"Main {DEFS_THEORY_NAME}",
            rows=excellent,
            header="质量筛选后留存的引理",
            allow_sorry=False,
        ),
        encoding="utf-8",
        newline="\n",
    )

    stage_rendered: Dict[str, tuple[int, int, int]] = {}
    for stage, file_stem in STAGE_FILE.items():
        # 阶段文件与已证引理库保持一致：只放本阶段“已证明且未淘汰”的引理；
        # 未证明的候选引理统一留在 all_constructed_lemmas.thy（以 sorry 留档）。
        stage_rows = [
            r for r in rows if str(r.get("source") or "") == stage
        ]
        # 即使本阶段没有产出也写出空文件，保持领域目录结构稳定
        # 每个阶段文件自包含：递归带入本阶段引理依赖的其他引理块
        stage_names = {str(r.get("name")) for r in stage_rows}
        merged = _with_dependency_closure(rows, stage_names)
        stage_rendered[file_stem] = (
            len(merged),
            sum(1 for row in merged if row.get("has_proof")),
            len(stage_rows),
        )
        (destination / f"{file_stem}.thy").write_text(
            _render_library_thy(
                file_stem,
                imports=f"Main {DEFS_THEORY_NAME}",
                rows=merged,
                header=f"{STAGE_LABEL[stage]}：{stage}",
                allow_sorry=True,
                dependency_rows=[r for r in merged if str(r.get("name")) not in stage_names],
            ),
            encoding="utf-8",
            newline="\n",
        )

    label_rendered: Dict[str, Dict[str, int]] = {}
    for label in LINEAR_LABEL_ORDER:
        label_rows = [r for r in rows if label in _row_linear_labels(r)]
        seed_names = {str(r.get("name")) for r in label_rows}
        merged = _with_dependency_closure(rows, seed_names)
        label_rendered[label] = {
            "lemmas": len(label_rows),
            "rendered": len(merged),
        }
        (destination / f"{linear_label_theory(label)}.thy").write_text(
            _render_library_thy(
                linear_label_theory(label),
                imports=f"Main {DEFS_THEORY_NAME}",
                rows=merged,
                header=f"线性标签：{LINEAR_LABEL_ZH.get(label, label)}（{label}）",
                allow_sorry=True,
                dependency_rows=[r for r in merged if str(r.get("name")) not in seed_names],
            ),
            encoding="utf-8",
            newline="\n",
        )

    csv_path = destination / STAGE_CSV
    with csv_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(
            [
                "序号",
                "引理名",
                "阶段",
                "来源",
                "所在文件",
                "是否在proven_lemmas.thy",
                "质量Q",
                "状态",
                "首次出现定理",
                "线性标签",
                "标签文件",
            ]
        )
        for idx, row in enumerate(rows, start=1):
            source = str(row.get("source") or "unknown")
            stage = STAGE_LABEL.get(source, "未分类")
            in_proven = bool(row.get("has_proof")) and str(row.get("status") or "") != "eliminated"
            q = (row.get("quality") or {}).get("q") if isinstance(row.get("quality"), Mapping) else None
            writer.writerow(
                [
                    idx,
                    row.get("name") or "",
                    stage,
                    source,
                    f"{STAGE_FILE.get(source, 'all_constructed_lemmas')}.thy",
                    "是" if in_proven else "否",
                    "" if q is None else q,
                    row.get("status") or "",
                    row.get("first_seen_theorem") or "",
                    "、".join(_row_linear_labels(row)),
                    "、".join(
                        f"{linear_label_theory(label)}.thy"
                        for label in _row_linear_labels(row)
                    ),
                ]
            )

    _write_json(
        destination / DOMAIN_LIBRARY_JSON,
        {
            "domain": domain,
            "summary": {
                "generated_total": len(rows),
                "with_proof": sum(1 for r in rows if r.get("has_proof")),
                "retained": len(excellent),
                "proven": len(proven_blocks or {}),
                "by_source": _count(rows, "source"),
                "by_linear_label": _count_linear_labels(rows),
                "by_linear_label_rendered": {
                    label: int(values["rendered"])
                    for label, values in label_rendered.items()
                },
                "by_stage_file": {
                    STAGE_FILE[k]: sum(1 for r in rows if str(r.get("source")) == k)
                    for k in STAGE_FILE
                },
            },
            "theorems": list(theorem_sources or {}),
            "lemmas": rows,
        },
    )

    lines = [
        f"领域：{domain}",
        "",
        f"all_constructed_lemmas.thy  （{len(rows)} 条）",
        "生成的所有引理（含未证明，未证明者以 sorry 留档）",
        "",
        f"excellent_lemmas.thy  （{len(excellent)} 条）",
        "质量筛选后留存的引理",
        "",
        f"proven_lemmas.thy  （{len(proven_blocks or {})} 条）",
        "所有证明成功的引理（含后续被淘汰者，跨定理共享）",
        "",
        "defs.thy 函数定义（领域全部定义，只增不减）",
        "",
    ]
    for _stage, file_stem in STAGE_FILE.items():
        total, proven, seeds = stage_rendered.get(file_stem, (0, 0, 0))
        extra = total - seeds
        lines.append(
            f"{file_stem}.thy  {total} 条（本阶段 {seeds} 条，依赖 {extra} 条）  "
            f"{proven} 条已证明"
        )
    lines.append("")
    lines.append("按线性标签归档（论文 3.2.1；含未证明者，多标签引理会出现在多个文件）：")
    for label in LINEAR_LABEL_ORDER:
        values = label_rendered.get(label, {"lemmas": 0, "rendered": 0})
        extra = int(values["rendered"]) - int(values["lemmas"])
        lines.append(
            f"{linear_label_theory(label)}.thy  "
            f"{values['rendered']} 条（本标签 {values['lemmas']} 条，依赖 {extra} 条）  "
            f"{LINEAR_LABEL_ZH.get(label, label)}"
        )
    lines.append("")
    (destination / DOMAIN_README).write_text(
        "\n".join(lines), encoding="utf-8", newline="\n"
    )

    if theorem_sources:
        _copy_theorem_outputs(destination, theorem_sources=theorem_sources)
    elif theorem_names:
        sources: Dict[str, Path] = {}
        for theorem in theorem_names:
            for candidate in (
                Path(output_dir) / "verified" / theorem / f"{theorem}.thy",
                theorem_theory_dir(output_dir, domain, theorem) / f"{theorem}.thy",
            ):
                if candidate.is_file():
                    sources[theorem] = candidate
                    break
        _copy_theorem_outputs(destination, theorem_sources=sources)

    return destination


def _count(rows: Sequence[Mapping[str, object]], key: str) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for row in rows:
        value = str(row.get(key) or "unknown")
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def export_domain_library_from_runs(
    output_dirs: Sequence[str | Path],
    *,
    domain: str,
    destination: str | Path,
    data_dir: str | Path,
    theorem_sources: Optional[Mapping[str, Path]] = None,
) -> Path:
    """把多次运行的产物合并导出为一个领域级目录（用于最终结果归档）。"""
    domain = normalize_domain(domain)
    documents = []
    for output_dir in output_dirs:
        payload = _load_json(
            Path(output_dir) / "results" / LIBRARY_DIRNAME / LIBRARY_JSON_FILENAME, {}
        )
        if isinstance(payload, dict):
            documents.append(payload)
    rows = merge_library_rows(documents)
    proven_blocks = _collect_proven_blocks(output_dirs, domain)
    defs_text = _merge_defs_from_data(data_dir, domain)
    return export_domain_library(
        output_dirs[0] if output_dirs else ".",
        domain,
        destination=destination,
        data_dir=data_dir,
        theorem_sources=theorem_sources,
        defs_text=defs_text,
        proven_blocks=proven_blocks,
        rows=rows,
    )
