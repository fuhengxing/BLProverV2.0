"""
论文 3.2：引理质量筛选——标签识别、差异化质量衰减与批次淘汰。

来源标签（3.2.1 之一）：
  - global：全局引理，由全局引理生成策略产出，来源系数 0.7；
  - middle：中间引理，由中间引理提取策略产出，来源系数 1.0；
  - repair：修复引理，由修复引理构造策略产出，来源系数 1.3。

线性标签（3.2.1 之二）：序列不变性 / 操作可执行性 / 递归终止性 / 序关系保持性；
不属于上述四类者记为非线性（nonlinear）。多标签取最小线性系数（保护最强）。

差异化质量衰减（3.2.2）：Delta_i = Delta0 * 来源系数 * 线性系数，Delta0 = 1.0；
批次更新：Q_{t+1}(i) = Q_t(i) - Delta_i；
淘汰（3.2.2）：Q(i) < Qmin = 1.0 时该引理被移出引理库。

Delta0/Qmin 先按实测 Q(i) 量级等比缩放 1/3 标定为 0.01（论文原值 0.03），
再随 Q_SCALE = 100 整体放大到 1.0（见 eval/quality_scale.py）：与放大后的 Q(i) 同量纲，
只改变量纲、不改变筛选行为，读数更像百分制。
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .quality_scale import (
    CALIBRATED_DECAY_BASE,
    CALIBRATED_Q_MIN,
    LEGACY_Q_SCALE,
    Q_SCALE,
)

SOURCE_GLOBAL = "global"
SOURCE_MIDDLE = "middle"
SOURCE_REPAIR = "repair"
SOURCE_LABELS: Tuple[str, ...] = (SOURCE_GLOBAL, SOURCE_MIDDLE, SOURCE_REPAIR)

LINEAR_SEQUENCE_INVARIANCE = "sequence_invariance"
LINEAR_OPERATION_EXECUTABILITY = "operation_executability"
LINEAR_RECURSION_TERMINATION = "recursion_termination"
LINEAR_ORDER_PRESERVATION = "order_preservation"
LINEAR_NONLINEAR = "nonlinear"
LINEAR_LABELS: Tuple[str, ...] = (
    LINEAR_SEQUENCE_INVARIANCE,
    LINEAR_OPERATION_EXECUTABILITY,
    LINEAR_RECURSION_TERMINATION,
    LINEAR_ORDER_PRESERVATION,
    LINEAR_NONLINEAR,
)

# Delta0 / Qmin：先按实测 Q(i) 量级标定（论文原值 0.03 的 1/3），再随 Q_SCALE 整体放大，
# 量纲与放大后的 Q(i) 一致（0.01 * 100 = 1.0）
DEFAULT_DECAY_BASE = CALIBRATED_DECAY_BASE * Q_SCALE
DEFAULT_Q_MIN = CALIBRATED_Q_MIN * Q_SCALE
DEFAULT_SOURCE_COEFFICIENTS: Dict[str, float] = {
    SOURCE_GLOBAL: 0.7,
    SOURCE_MIDDLE: 1.0,
    SOURCE_REPAIR: 1.3,
}
DEFAULT_LINEAR_COEFFICIENTS: Dict[str, float] = {
    LINEAR_SEQUENCE_INVARIANCE: 0.7,
    LINEAR_OPERATION_EXECUTABILITY: 0.8,
    LINEAR_RECURSION_TERMINATION: 0.9,
    LINEAR_ORDER_PRESERVATION: 0.8,
    LINEAR_NONLINEAR: 1.2,
}

# 论文 3.2.1 列出的识别信号（引理陈述或证明脚本中出现的线索）。
LINEAR_SIGNALS: Dict[str, Tuple[str, ...]] = {
    LINEAR_SEQUENCE_INVARIANCE: (
        r"length",
        r"size",
        r"capacity",
        r"sorted",
        r"distinct",
        r"unique",
        r"LIFO|FIFO",
        r"sublist",
        r"set \|",
        r"\\<in>\s*set",
        r"alist_of[^=\n]*=[^=\n]*alist_of",
        r"map\s+fst",
        r"map\s+snd",
    ),
    LINEAR_OPERATION_EXECUTABILITY: (
        r"is_empty",
        r"\\<not>\s*[^\n]{0,24}empty",
        r"\\<noteq>\s*\[\]",
        r"\bfull\b",
        r"\\<in>\s*set\s*\|",
        r"\bexists\b",
        r"\bthe\s*\(",
        r"\bhd\b",
        r"\bindex\b",
        r"\bnth\b",
        r"\bnonempty\b",
    ),
    LINEAR_RECURSION_TERMINATION: (
        r"length[^\n]{0,16}<",
        r"<[^\n]{0,16}length",
        r"length[^\n]{0,16}\\<le>",
        r"sublist",
        r"decreases",
        r"termination",
        r"measure",
        r"\brec\b",
        r"interval",
    ),
    LINEAR_ORDER_PRESERVATION: (
        r"\bsorted\b",
        r"\bmin\b",
        r"\bmax\b",
        r"\btransitive\b",
        r"monotone",
        r"\\<le>",
        r"priority[^\n]{0,48}\\<le>",
        r"\+[^\n=]*=[^\n]*\+",
    ),
}


def identify_linear_labels(
    statement: str,
    *,
    explicit: Optional[Sequence[str]] = None,
) -> List[str]:
    """识别一条引理的线性标签（论文 3.2.1）；无任何命中时记为非线性。"""
    if explicit:
        ordered = [l for l in dict.fromkeys(explicit) if l in DEFAULT_LINEAR_COEFFICIENTS]
        if ordered:
            return ordered
    text = statement or ""
    hits: List[str] = []
    for label in (
        LINEAR_SEQUENCE_INVARIANCE,
        LINEAR_OPERATION_EXECUTABILITY,
        LINEAR_RECURSION_TERMINATION,
        LINEAR_ORDER_PRESERVATION,
    ):
        if any(re.search(pattern, text) for pattern in LINEAR_SIGNALS[label]):
            hits.append(label)
    return hits or [LINEAR_NONLINEAR]

LINEAR_LABEL_ALIASES: Dict[str, Tuple[str, ...]] = {
    LINEAR_NONLINEAR: (
        "nonlinear",
        "non linear",
        "not linear",
    ),
    LINEAR_ORDER_PRESERVATION: (
        "order preservation",
        "order preserving",
        "order relation",
        "ordering",
        "sorted",
        "ascending",
        "non decreasing",
        "nondecreasing",
        "monotone",
        "monotonic",
        "minimum",
        "minimal",
        "maximum",
        "maximal",
    ),
    LINEAR_RECURSION_TERMINATION: (
        "recursion termination",
        "recursive termination",
        "termination",
        "terminates",
        "terminating",
        "well founded",
        "decreasing",
        "decreases",
        "measure",
        "recursion depth",
        "base case",
    ),
    LINEAR_OPERATION_EXECUTABILITY: (
        "operation executability",
        "executability",
        "executable",
        "well defined",
        "definedness",
        "precondition",
        "non empty",
        "nonempty",
        "defined on",
        "can be applied",
        "index bounds",
        "in range",
    ),
    LINEAR_SEQUENCE_INVARIANCE: (
        "sequence invariance",
        "sequence invariant",
        "invariance",
        "invariant preserved",
        "permutation",
        "multiset",
        "same elements",
        "length preserved",
        "size preserved",
        "structure preserved",
        "sequence",
    ),
}

_ALIAS_PRIORITY: Tuple[str, ...] = (
    LINEAR_SEQUENCE_INVARIANCE,
    LINEAR_OPERATION_EXECUTABILITY,
    LINEAR_RECURSION_TERMINATION,
    LINEAR_ORDER_PRESERVATION,
    LINEAR_NONLINEAR,
)


def _normalize_label_text(text: object) -> str:
    s = str(text or "").strip().lower()
    s = s.replace("_", " ").replace("-", " ")
    s = re.sub(r"\s+", " ", s)
    return s.strip(" .:*`\"'()[]")


def _append_unique(seq: List[str], item: str) -> None:
    if item and item not in seq:
        seq.append(item)


def canonicalize_linear_labels(value: object) -> List[str]:
    """
    论文 3.2.1（方案 C）：将模型给出的线性标签自由文本规范化为规范标签。

    - 接受单标签、逗号/分号分隔的多标签或自由描述；
    - 先做规范名精确匹配，再退化为关键词匹配；
    - 无法识别时返回 []（调用方应回退到基于陈述的正则识别）。
    """
    if value is None:
        return []
    if isinstance(value, str):
        items = re.split(r"[,;/、，；|]+", value)
    elif isinstance(value, (list, tuple, set)):
        items = [str(v) for v in value]
    else:
        items = [str(value)]

    normalized_names = {_normalize_label_text(l): l for l in LINEAR_LABELS}
    canonical: List[str] = []
    for item in items:
        norm = _normalize_label_text(item)
        if not norm:
            continue
        exact = normalized_names.get(norm)
        if exact:
            _append_unique(canonical, exact)
            continue
        for label in _match_alias_labels(norm):
            _append_unique(canonical, label)

    if LINEAR_NONLINEAR in canonical and len(canonical) > 1:
        canonical = [l for l in canonical if l != LINEAR_NONLINEAR]
    canonical.sort(key=lambda l: _ALIAS_PRIORITY.index(l) if l in _ALIAS_PRIORITY else 99)
    return canonical


def _match_alias_labels(norm: str) -> List[str]:
    """"按别名长度优先消费文本，避免「non decreasing」被误判为递归终止。"""
    work = " " + norm + " "
    pairs = [
        (alias.replace("-", " "), label)
        for label, aliases in LINEAR_LABEL_ALIASES.items()
        for alias in aliases
    ]
    pairs.sort(key=lambda x: -len(x[0]))
    found: List[str] = []
    for alias, label in pairs:
        if alias and alias in work:
            found.append(label)
            work = work.replace(alias, " ")
    return found


def source_coefficient(
    source: str,
    coefficients: Optional[Mapping[str, float]] = None,
) -> float:
    """论文表 3-2：来源系数（未知来源按中间引理处理）。"""
    coeffs = coefficients or DEFAULT_SOURCE_COEFFICIENTS
    return float(coeffs.get(source, coeffs[SOURCE_MIDDLE]))


def linear_coefficient(
    labels: Optional[Sequence[str]],
    coefficients: Optional[Mapping[str, float]] = None,
) -> float:
    """论文表 3-3：线性系数，多标签取最小值（关联越紧密保护越强）。"""
    coeffs = coefficients or DEFAULT_LINEAR_COEFFICIENTS
    values = [coeffs[label] for label in (labels or []) if label in coeffs]
    if not values:
        return float(coeffs[LINEAR_NONLINEAR])
    return float(min(values))


def decay_value(
    source: str,
    linear_labels: Optional[Sequence[str]],
    *,
    base: float = DEFAULT_DECAY_BASE,
    source_coefficients: Optional[Mapping[str, float]] = None,
    linear_coefficients: Optional[Mapping[str, float]] = None,
) -> float:
    """论文 3.2.2：Delta_i = Delta0 * 来源系数 * 线性系数。"""
    return round(
        base
        * source_coefficient(source, source_coefficients)
        * linear_coefficient(linear_labels, linear_coefficients),
        6,
    )


@dataclass
class ScreeningOutcome:
    """一轮批次筛选的产物（3.2.3 步骤七至步骤九）。"""

    updated: Dict[str, dict] = field(default_factory=dict)
    removed: List[str] = field(default_factory=list)
    retained_dependencies: List[str] = field(default_factory=list)
    total: int = 0
    eliminated_count: int = 0
    q_min: float = DEFAULT_Q_MIN
    decay_base: float = DEFAULT_DECAY_BASE

    @property
    def elimination_rate(self) -> float:
        """淘汰率 = 本轮被移出引理库的引理数 / 本轮参与筛选的引理总数。"""
        if self.total <= 0:
            return 0.0
        return round(self.eliminated_count / self.total, 4)

    def to_dict(self) -> Dict[str, object]:
        return {
            "total": self.total,
            "eliminated_count": self.eliminated_count,
            "elimination_rate": self.elimination_rate,
            "removed": list(self.removed),
            "retained_dependencies": list(self.retained_dependencies),
            "q_min": self.q_min,
            "decay_base": self.decay_base,
            "updated": self.updated,
        }


def _dependency_closed_removal(
    removed: Sequence[str],
    direct: Mapping[str, Sequence[str]],
) -> Tuple[List[str], List[str]]:
    """
    依赖安全删除：若某被淘汰引理仍被库内保留引理直接调用，则本轮回退保留它，
    避免移出后引理库因悬空引用而不可验证。返回 (最终删除, 回退保留)。
    """
    drop = set(removed)
    changed = True
    while changed:
        changed = False
        for name, deps in direct.items():
            if name in drop:
                continue
            for dep in deps:
                if dep in drop:
                    drop.discard(dep)
                    changed = True
    final = [n for n in removed if n in drop]
    retained = [n for n in removed if n not in drop]
    return final, retained


def screen_batch(
    scores: Mapping[str, Mapping[str, object]],
    *,
    source_by_lemma: Optional[Mapping[str, str]] = None,
    linear_by_lemma: Optional[Mapping[str, Sequence[str]]] = None,
    statements: Optional[Mapping[str, str]] = None,
    direct_dependencies: Optional[Mapping[str, Sequence[str]]] = None,
    previous_q: Optional[Mapping[str, float]] = None,
    base: float = DEFAULT_DECAY_BASE,
    q_min: float = DEFAULT_Q_MIN,
    source_coefficients: Optional[Mapping[str, float]] = None,
    linear_coefficients: Optional[Mapping[str, float]] = None,
    dependency_safe_removal: bool = True,
) -> ScreeningOutcome:
    """
    论文 3.2.2/3.2.3：对一批引理执行差异化质量衰减，并淘汰低于阈值的引理。

    :param scores: {name: {s, d, u, q}}，q 为当前批次前的综合质量评分
    :param source_by_lemma: {name: global|middle|repair}
    :param linear_by_lemma: {name: [线性标签]}
    :param statements: {name: 引理陈述/脚本}，未显式给出线性标签时用于识别
    :param direct_dependencies: {name: [直接依赖的库内引理名]}，用于依赖安全删除
    :param previous_q: {name: 上一批次筛选后的 Q(i)}，实现 Q_{t+1}=Q_t-Delta_i 的累积衰减
    """
    source_by_lemma = source_by_lemma or {}
    linear_by_lemma = linear_by_lemma or {}
    statements = statements or {}
    previous_q = previous_q or {}
    updated: Dict[str, dict] = {}
    removed: List[str] = []

    for name, entry in scores.items():
        row = dict(entry)
        source = str(source_by_lemma.get(name) or SOURCE_MIDDLE)
        raw_labels = linear_by_lemma.get(name)
        if raw_labels:
            labels = list(dict.fromkeys(raw_labels))
        else:
            labels = identify_linear_labels(statements.get(name, ""))
        delta = decay_value(
            source,
            labels,
            base=base,
            source_coefficients=source_coefficients,
            linear_coefficients=linear_coefficients,
        )
        q_base = float(row.get("q", 0.0) or 0.0)
        # 论文 3.2.2：已有引理从上一批次筛选后的 Q 继续衰减；新引理从本次评分 Q 起算
        q_prev = float(previous_q[name]) if name in previous_q else q_base
        q_raw = q_prev - delta
        row.update(
            {
                "source": source,
                "linear_labels": list(labels),
                "delta": delta,
                "q_base": round(q_base, 6),
                "q": max(round(q_raw, 6), 0.0),
            }
        )
        below_qmin = q_raw < q_min
        row["below_qmin"] = below_qmin
        row["eliminated"] = below_qmin
        if below_qmin:
            removed.append(name)
        updated[name] = row

    # 论文 3.2.2：Q(i) < Qmin 移出引理库（依赖安全：仍被保留引理引用者回退保留）
    final_removed = removed
    retained_dep: List[str] = []
    if dependency_safe_removal and removed and direct_dependencies:
        final_removed, retained_dep = _dependency_closed_removal(
            removed, direct_dependencies
        )
    for name in retained_dep:
        updated[name]["eliminated"] = False
        updated[name]["retained_for_dependency"] = True

    return ScreeningOutcome(
        updated=updated,
        removed=list(final_removed),
        retained_dependencies=list(retained_dep),
        total=len(updated),
        eliminated_count=len(final_removed),
        q_min=q_min,
        decay_base=base,
    )


LABELS_FILENAME = "lemma_labels.json"


def labels_file_path(output_dir: str | Path) -> Path:
    return Path(output_dir) / "results" / "proven_lemmas" / LABELS_FILENAME


def load_labels(output_dir: str | Path) -> Dict[str, dict]:
    path = labels_file_path(output_dir)
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return data if isinstance(data, dict) else {}


def record_labels(output_dir: str | Path, mapping: Mapping[str, Mapping[str, object]]) -> None:
    """持久化引理的来源标签与线性标签（供后续批次筛选与来源系数取用）。"""
    path = labels_file_path(output_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = load_labels(output_dir)
    for name, info in (mapping or {}).items():
        if not name:
            continue
        entry = dict(data.get(name, {}))
        source = info.get("source") if isinstance(info, Mapping) else None
        if source:
            entry["source"] = str(source)
        labels = info.get("linear_labels") if isinstance(info, Mapping) else None
        if labels:
            entry["linear_labels"] = list(labels)
        origin = (
            info.get("linear_label_source") if isinstance(info, Mapping) else None
        )
        if origin:
            entry["linear_label_source"] = str(origin)
        data[name] = entry
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


def source_map_from_labels(data: Mapping[str, dict]) -> Dict[str, str]:
    return {
        name: str(info.get("source"))
        for name, info in (data or {}).items()
        if isinstance(info, Mapping) and info.get("source")
    }


def linear_map_from_labels(data: Mapping[str, dict]) -> Dict[str, List[str]]:
    out: Dict[str, List[str]] = {}
    for name, info in (data or {}).items():
        if isinstance(info, Mapping) and info.get("linear_labels"):
            out[name] = list(info["linear_labels"])
    return out

STATE_FILENAME = "quality_screening_state.json"
STATE_SCALE_KEY = "_scale"
"""落盘文件中的量纲标记载：读取时据此把历史量纲换算为当前量纲。"""


def state_file_path(output_dir: str | Path) -> Path:
    return Path(output_dir) / "results" / "proven_lemmas" / STATE_FILENAME


def load_state(output_dir: str | Path) -> Dict[str, float]:
    """读取上一批次筛选后的 Q(i) 运行值 {name: q}（用于累积衰减）。

    兼容量纲放大（Q_SCALE）前的历史落盘：旧文件没有量纲标记载，按未放大量纲
    （LEGACY_Q_SCALE）换算到当前量纲，避免历史 run 因量纲不一致被整体淘汰。
    """
    path = state_file_path(output_dir)
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if not isinstance(data, dict):
        return {}
    marker = data.get(STATE_SCALE_KEY)
    from_scale = (
        float(marker)
        if isinstance(marker, (int, float)) and float(marker) > 0
        else LEGACY_Q_SCALE
    )
    factor = Q_SCALE / from_scale
    return {
        str(k): round(float(v) * factor, 6)
        for k, v in data.items()
        if not str(k).startswith("_") and isinstance(v, (int, float))
    }


def save_state(output_dir: str | Path, q_map: Mapping[str, float]) -> None:
    """持久化本批次筛选后的 Q(i) 运行值（附 _scale 量纲标记）。"""
    path = state_file_path(output_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {STATE_SCALE_KEY: Q_SCALE}
    payload.update({str(k): round(float(v), 6) for k, v in (q_map or {}).items()})
    path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
    )
