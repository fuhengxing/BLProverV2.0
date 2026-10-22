"""
引理管理模块
"""

from .lemma_cache import LemmaCache, chroma_embedding_function_for_config
from .lemma_matcher import LemmaMatcher, MatchType
from .lemma import Lemma
from .unproven_lemma_store import UnprovenLemmaStore
from .lemmas_reflection import (
    LemmasReflectionRunner,
    LemmasReflectionResult,
    parse_lemmas_reflection_json,
    verify_unproven_lemmas_thy,
)
from .proven_lemma_store import ProvenLemmaStore, PROVEN_THEORY_NAME
from .definition_store import DefinitionStore
from .domain import normalize_domain, resolve_domain, theorem_theory_dir
from .thy_imports import DEFS_THEORY_NAME

__all__ = [
    "LemmaCache",
    "LemmaMatcher",
    "MatchType",
    "Lemma",
    "UnprovenLemmaStore",
    "LemmasReflectionRunner",
    "LemmasReflectionResult",
    "parse_lemmas_reflection_json",
    "verify_unproven_lemmas_thy",
    "ProvenLemmaStore",
    "DefinitionStore",
    "PROVEN_THEORY_NAME",
    "DEFS_THEORY_NAME",
    "resolve_domain",
    "normalize_domain",
    "theorem_theory_dir",
    "chroma_embedding_function_for_config",
]
