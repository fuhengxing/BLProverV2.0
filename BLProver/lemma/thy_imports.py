"""全局 / 定理目录 .thy 的 imports 行约定（定理位于 theory/<domain>/<theorem>/）。"""

from __future__ import annotations

import re

DEFS_THEORY_NAME = "defs"
PROVEN_THEORY_NAME = "proven_lemmas"

_LEGACY_DOMAIN_IMPORT_RE = re.compile(
    r'"\.\./([^"/]+)/(defs|proven_lemmas)"'
)


def domain_defs_import_path(domain: str) -> str:
    del domain
    return f'"../{DEFS_THEORY_NAME}"'


def domain_proven_import_path(domain: str) -> str:
    del domain
    return f'"../{PROVEN_THEORY_NAME}"'


def rewrite_theorem_thy_imports(text: str) -> str:
    """将旧版 ../<domain>/defs|proven_lemmas 改为 ../defs|proven_lemmas。"""

    def _repl(match: re.Match[str]) -> str:
        return f'"../{match.group(2)}"'

    return _LEGACY_DOMAIN_IMPORT_RE.sub(_repl, text or "")


def domain_defs_imports(*, packages: str = "Main") -> str:
    """领域目录内 proven_lemmas.thy 引用同目录 defs。"""
    return f"{packages} {DEFS_THEORY_NAME}"


def domain_defs_thy_imports(*, packages: str = "Main") -> str:
    """领域目录内 defs.thy。"""
    return packages


def theorem_defs_imports(*, packages: str = "Main", domain: str) -> str:
    return f"{packages} {domain_defs_import_path(domain)}"


def theorem_unproven_imports(*, packages: str = "Main", domain: str) -> str:
    """定理目录 unproven_lemmas.thy：defs + 领域 proven_lemmas（与 sketch 一致，便于引理证明复用已证库）。"""
    return (
        f"{packages} {domain_defs_import_path(domain)} "
        f"{domain_proven_import_path(domain)}"
    )


def theorem_sketch_imports(
    *, packages: str = "Main", domain: str, unproven_thy_name: str
) -> str:
    return (
        f"{packages} {domain_defs_import_path(domain)} "
        f"{domain_proven_import_path(domain)} "
        f'"{unproven_thy_name}"'
    )


def theorem_final_imports(*, packages: str = "Main", domain: str) -> str:
    return (
        f"{packages} {domain_defs_import_path(domain)} "
        f"{domain_proven_import_path(domain)}"
    )


def theorem_self_contained_imports(*, packages: str = "Main") -> str:
    """自包含最终定理 .thy：只 imports 基础理论（默认 Main），不导入自定义引理库。"""
    return packages or "Main"


def import_theory_name_from_path(import_path: str) -> str:
    """将 imports 中的 \"../stack/defs\" 解析为 Isabelle 理论名 defs。"""
    text = (import_path or "").strip().strip('"').strip("'")
    if not text:
        return ""
    name = text.replace("\\", "/").rstrip("/").split("/")[-1]
    return name
