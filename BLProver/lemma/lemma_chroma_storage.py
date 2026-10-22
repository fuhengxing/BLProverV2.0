"""
ChromaDB-backed lemma storage (embedded PersistentClient).
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict
from typing import Any, Dict, List, Optional, Tuple

import chromadb
from chromadb.utils import embedding_functions

from ..utils.isabelle_parser import IsabelleParser
from .lemma import Lemma


def _stable_lemma_id(statement: str) -> str:
    normalized = IsabelleParser.normalize_statement(statement)
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    return f"lemma_{digest}"


def default_embedding_function():
    # IMPORTANT: keep embedding choice explicit/stable.
    # Auto-switching based on env (e.g., OPENAI_API_KEY) can cause persisted
    # collection conflicts: openai vs default.
    return embedding_functions.DefaultEmbeddingFunction()


class LemmaChromaStorage:
    """
    Store lemmas in ChromaDB and query them by vector similarity.
    """

    def __init__(
        self,
        chroma_path: str,
        collection_name: str = "proven_lemma_chromadb",
        embedding_function=None,
    ):
        self._client = chromadb.PersistentClient(path=chroma_path)
        self._collection = self._client.get_or_create_collection(
            name=collection_name,
            embedding_function=embedding_function or default_embedding_function(),
        )

    @staticmethod
    def lemma_id(statement: str) -> str:
        return _stable_lemma_id(statement)

    def upsert_lemma(self, lemma: Lemma) -> str:
        lemma_id = self.lemma_id(lemma.statement)

        # Chroma metadata values must be JSON-serializable primitives.
        meta = asdict(lemma)
        # Keep statement in documents; remove large/text fields from metadata.
        meta.pop("statement", None)
        proof = meta.pop("proof", "")
        metadata_blob = meta.pop("metadata", {})  # user metadata dict
        meta["proof"] = proof
        meta["metadata_json"] = json.dumps(metadata_blob, ensure_ascii=False)

        self._collection.upsert(
            ids=[lemma_id],
            documents=[lemma.statement],
            metadatas=[meta],
        )
        return lemma_id

    def delete_lemma(self, statement: str) -> bool:
        lemma_id = self.lemma_id(statement)
        self._collection.delete(ids=[lemma_id])
        return True

    def get_lemma(self, statement: str) -> Optional[Lemma]:
        lemma_id = self.lemma_id(statement)
        got = self._collection.get(ids=[lemma_id], include=["documents", "metadatas"])
        if not got["ids"]:
            return None
        doc = got["documents"][0]
        meta = got["metadatas"][0] or {}
        return _lemma_from_chroma(doc, meta)

    def count(self) -> int:
        # Chroma doesn't expose a fast count in all backends; use get with limit.
        # For typical lemma caches this is fine.
        got = self._collection.get(include=[], limit=1)
        # When include=[] and limit=1, ids length is <=1; can't count. Fall back:
        got_all = self._collection.get(include=[], limit=10_000_000)
        return len(got_all["ids"])

    def get_all(self) -> List[Lemma]:
        got = self._collection.get(include=["documents", "metadatas"], limit=10_000_000)
        docs = got.get("documents") or []
        metas = got.get("metadatas") or []
        out: List[Lemma] = []
        for doc, meta in zip(docs, metas):
            out.append(_lemma_from_chroma(doc, meta or {}))
        return out

    def query(
        self,
        query_text: str,
        k: int = 5,
        where: Optional[Dict[str, Any]] = None,
    ) -> List[Tuple[Lemma, float]]:
        res = self._collection.query(
            query_texts=[query_text],
            n_results=k,
            where=where,
            include=["documents", "metadatas", "distances"],
        )
        docs = res["documents"][0]
        metas = res["metadatas"][0]
        dists = res["distances"][0]
        out: List[Tuple[Lemma, float]] = []
        for doc, meta, dist in zip(docs, metas, dists):
            out.append((_lemma_from_chroma(doc, meta or {}), float(dist)))
        return out


def _lemma_from_chroma(document: str, meta: Dict[str, Any]) -> Lemma:
    metadata_json = meta.get("metadata_json") or "{}"
    try:
        user_meta = json.loads(metadata_json)
    except Exception:
        user_meta = {}

    return Lemma(
        statement=document,
        proof=str(meta.get("proof", "")),
        status=str(meta.get("status", "unverified")),
        usage_count=int(meta.get("usage_count", 0)),
        score=float(meta.get("score", 0.0)),
        metadata=user_meta if isinstance(user_meta, dict) else {},
        created_at=str(meta.get("created_at", "")),
        updated_at=str(meta.get("updated_at", "")),
    )

