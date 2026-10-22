"""
维度 3：引理复用性评估（U(i)）。

U(i) = 全局 proven_lemmas.thy 中第 i 条引理被不同定理的 proof 显式引用的次数。
每次验证新定理后，从该定理的 usage 记录中的 external_refs 提取 proven 库引理引用。
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Dict, List, Set

logger = logging.getLogger(__name__)

USAGE_HISTORY_FILENAME = "lemma_usage_history.json"


class LemmaUsageHistory:
    """
    持久化的引理被引用历史：
    {lemma_name: set(theorem_names)}

    每次新定理成功验证后调用 record_lemma_usage() 更新。
    """

    def __init__(self, output_dir: str | Path):
        self._output_dir = Path(output_dir)
        self._path = (
            self._output_dir / "results" / "proven_lemmas" / USAGE_HISTORY_FILENAME
        )
        self._data: Dict[str, Set[str]] = self._load()

    def _load(self) -> Dict[str, Set[str]]:
        if not self._path.is_file():
            return {}
        try:
            raw: Dict[str, List[str]] = json.loads(
                self._path.read_text(encoding="utf-8")
            )
            return {k: set(v) for k, v in raw.items()}
        except Exception as exc:
            logger.warning("引理被引用历史加载失败: %s", exc)
            return {}

    def _save(self) -> None:
        self._path.parent.mkdir(parents=True, exist_ok=True)
        serializable: Dict[str, List[str]] = {
            k: sorted(v) for k, v in self._data.items()
        }
        self._path.write_text(
            json.dumps(serializable, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

    def record_lemma_usage(self, lemma_names: List[str], theorem_name: str) -> None:
        """
        记录某定理的 proof 引用了 proven_lemmas 中的这些引理。
        lemma_names 来自 theorem 的 external_refs（不在 unproven 中）。
        """
        changed = False
        for name in lemma_names:
            if not name:
                continue
            if name not in self._data:
                self._data[name] = set()
            if theorem_name not in self._data[name]:
                self._data[name].add(theorem_name)
                changed = True
        if changed:
            self._save()

    def get_reuse_count(self, lemma_name: str) -> int:
        """U(i)：引理被多少不同定理引用。"""
        return len(self._data.get(lemma_name, set()))

    def get_all_counts(self) -> Dict[str, int]:
        return {k: len(v) for k, v in self._data.items()}


class LemmaReuseScorer:
    """引理复用性评分器：从 UsageHistory 读取 U(i)。"""

    def __init__(self, output_dir: str | Path):
        self._history = LemmaUsageHistory(output_dir)

    def score_all(self, lemma_names: List[str]) -> Dict[str, int]:
        counts = self._history.get_all_counts()
        return {name: counts.get(name, 1) for name in lemma_names}
