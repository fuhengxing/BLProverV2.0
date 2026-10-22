"""
论文 2.4.1 / 2.4.2：引理矢量存储与基于余弦相似度的冗余判重。

- 每条存储条目 = 文档（引理陈述/证明）+ 元数据（数据结构、生成阶段）+ 嵌入向量。
- 未证明引理存储与已证明引理存储分离（namespace = unproven / proven）。
- 收录条件：候选引理与库内**所有**已有引理的余弦相似度均 < 阈值（论文 2.4.2，默认 0.92）。

嵌入器默认使用确定性词袋嵌入（无外部依赖）；若注入外部嵌入器（如 Chroma/OpenAI
嵌入函数），调用方可直接替换，判重逻辑不变。
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

DEFAULT_DIM = 256
DEFAULT_SIMILARITY_THRESHOLD = 0.92

_TOKEN_RE = re.compile(r'"[^"]*"|\w+|[^\w\s]')
_LEMMA_HEAD_RE = re.compile(
    r"^\s*(?:lemma|theorem|corollary|proposition)\s+[A-Za-z0-9_']+\s*:?\s*",
    re.IGNORECASE,
)


def strip_lemma_head(text: str) -> str:
    """去掉引理名（名称只是标识，不参与语义判重）。"""
    return _LEMMA_HEAD_RE.sub("", text or "", count=1)


def _bag_tokens(text: str) -> List[str]:
    """保留字符串字面量与符号的 token 序列（小写）。"""
    return [tok.lower() for tok in _TOKEN_RE.findall(text or "")]


class LexicalEmbedder:
    """确定性词袋嵌入：token 哈希入桶计数后 L2 归一化。"""

    def __init__(self, dim: int = DEFAULT_DIM):
        self.dim = dim

    def embed(self, text: str) -> List[float]:
        vec = [0.0] * self.dim
        for tok in _bag_tokens(text):
            digest = hashlib.md5(tok.encode("utf-8")).hexdigest()
            vec[int(digest[:8], 16) % self.dim] += 1.0
        norm = math.sqrt(sum(v * v for v in vec))
        if norm == 0.0:
            return vec
        return [v / norm for v in vec]


def cosine_similarity(a: Sequence[float], b: Sequence[float]) -> float:
    """余弦相似度；维度不一致或空向量返回 0。"""
    if not a or not b or len(a) != len(b):
        return 0.0
    return float(sum(x * y for x, y in zip(a, b)))


class LemmaVectorStore:
    """按命名空间持久化的引理嵌入存储（论文 2.4.1）。"""

    def __init__(
        self,
        output_dir: str | Path,
        stem: str,
        *,
        embedder: Optional[object] = None,
        dim: int = DEFAULT_DIM,
    ):
        self.path = (
            Path(output_dir) / "results" / "proven_lemmas" / f"{stem}.json"
        )
        self.embedder = embedder or LexicalEmbedder(dim)
        self._vectors: Dict[str, List[float]] = {}
        self._load()

    # ---- 持久化 ----
    def _load(self) -> None:
        if not self.path.is_file():
            return
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
        except Exception:
            return
        if isinstance(data, dict):
            self._vectors = {
                str(k): [float(x) for x in v]
                for k, v in data.items()
                if isinstance(v, list) and v
            }

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(
            json.dumps(self._vectors, ensure_ascii=False), encoding="utf-8"
        )

    # ---- 写入 ----
    def embed(self, text: str) -> List[float]:
        text = strip_lemma_head(text)
        fn = getattr(self.embedder, "embed", None)
        if callable(fn):
            return list(fn(text))
        return list(self.embedder(text))  # type: ignore[misc]

    def add(self, name: str, text: str) -> None:
        if name:
            self._vectors[name] = self.embed(text)

    def remove(self, names: Iterable[str]) -> None:
        for name in names or ():
            self._vectors.pop(name, None)

    def names(self) -> List[str]:
        return list(self._vectors.keys())

    # ---- 查询 ----
    def max_similarity(self, text: str) -> Tuple[float, Optional[str]]:
        """返回与库内所有已有引理的最大余弦相似度及其引理名。"""
        if not self._vectors:
            return 0.0, None
        vec = self.embed(text)
        best_sim = 0.0
        best_name: Optional[str] = None
        for name, other in self._vectors.items():
            sim = cosine_similarity(vec, other)
            if sim > best_sim:
                best_sim, best_name = sim, name
        return best_sim, best_name

    def is_duplicate(
        self,
        text: str,
        threshold: float = DEFAULT_SIMILARITY_THRESHOLD,
    ) -> Tuple[bool, Optional[str], float]:
        """论文 2.4.2：与库内任一引理相似度 >= 阈值即视为语义重复。"""
        sim, name = self.max_similarity(text)
        is_dup = name is not None and sim >= threshold
        return is_dup, (name if is_dup else None), sim

    def sync(self, blocks: Mapping[str, str], *, overwrite: bool = False) -> None:
        """把库内引理补齐嵌入（用于既有引理库首次建立向量存储）。"""
        for name, block in (blocks or {}).items():
            if name and (overwrite or name not in self._vectors):
                self.add(name, block)