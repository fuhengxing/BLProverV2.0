"""
主定理验证通过后的引理证明编排：对 unproven_lemmas.thy 中全部 sorry 引理迭代证明。
"""

from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from ..lemma.definition_store import DefinitionStore
from ..lemma.lemma import Lemma
from ..lemma.lemma_cache import LemmaCache
from ..lemma.proven_lemma_store import ProvenLemmaStore
from ..utils.isabelle_sledgehammer import (
    IsabelleRunnerConfig,
    IsabelleServerSessionPool,
    prepare_session_for_lemma_proof_verify,
)
from .iterator import (
    LemmaProofIterator,
    lemma_block_text,
    reset_lemma_to_sorry,
    summarize_lemma_proof_result,
    verify_single_lemma_light,
    verify_then_sledgehammer,
)
from .usage import (
    LemmaUsageEntry,
    TheoremLemmaUsageReport,
    lemma_blocks_in_thy,
    lemma_still_sorry,
)

logger = logging.getLogger(__name__)

_LEMMA_HEAD_LINE = re.compile(
    r"^\s*(lemma|theorem|corollary|proposition)\s+(\S+|\(\S+\))\s*(:|\s)",
    re.IGNORECASE,
)
_PROOF_BODY_START = re.compile(
    r"^\s*(proof|by|using|apply|have|from|show\b|next\b|qed\b|-\s*$)",
    re.IGNORECASE,
)


def _lemma_block_verified(lemma_text: str, name: str) -> bool:
    block = lemma_block_text(lemma_text, name)
    if not block:
        return False
    if lemma_still_sorry(block):
        return False
    return "sledgehammer" not in block.lower()


def _all_unproven_lemmas_satisfied(unproven_text: str) -> bool:
    """unproven 中全部引理须已证且无 sledgehammer；无引理块时视为已满足。"""
    blocks = lemma_blocks_in_thy(unproven_text)
    if not blocks:
        return True
    for name in blocks:
        if not _lemma_block_verified(unproven_text, name):
            return False
    return True


def _stmt_by_name_from_usage(usage: TheoremLemmaUsageReport) -> Dict[str, str]:
    return {
        e.name: e.statement
        for e in (*usage.used, *usage.unused)
        if e.statement.strip()
    }


def _used_lemma_names(usage: TheoremLemmaUsageReport) -> set[str]:
    return {e.name for e in usage.used}


def _sorry_targets_from_unproven(
    unproven_text: str,
    usage: TheoremLemmaUsageReport,
) -> List[LemmaUsageEntry]:
    """从 unproven .thy 收集全部仍为 sorry 的引理（不按主定理引用筛选）。"""
    blocks = lemma_blocks_in_thy(unproven_text)
    stmt_by_name = _stmt_by_name_from_usage(usage)
    targets: List[LemmaUsageEntry] = []
    for name in sorted(blocks.keys()):
        block = blocks[name]
        if not lemma_still_sorry(block):
            continue
        targets.append(
            LemmaUsageEntry(
                name=name,
                statement=stmt_by_name.get(name, block),
                still_sorry=True,
                source="unproven",
            )
        )
    return targets


def _split_sorry_targets(
    targets: List[LemmaUsageEntry],
    usage: TheoremLemmaUsageReport,
) -> Tuple[List[LemmaUsageEntry], List[LemmaUsageEntry]]:
    """按主定理是否引用，将待证引理分为 used / unused 两组（均保持字母序）。"""
    used_names = _used_lemma_names(usage)
    used = [t for t in targets if t.name in used_names]
    unused = [t for t in targets if t.name not in used_names]
    return used, unused


def _block_with_sorry_proof(block: str) -> str:
    """将引理块恢复为仅含陈述 + sorry 的形式（保留 assumes/shows 行）。"""
    block = block.strip()
    if not block:
        return block
    if lemma_still_sorry(block):
        return block
    lines = block.splitlines()
    kept: list[str] = []
    seen_shows = False
    for line in lines:
        m = _LEMMA_HEAD_LINE.match(line)
        if m:
            kept = [line]
            seen_shows = False
            continue
        if not kept:
            continue
        if _PROOF_BODY_START.match(line):
            break
        kept.append(line)
        if re.match(r"^\s*shows\b", line):
            seen_shows = True
        elif seen_shows and not re.match(r"^\s*(assumes|shows)\b", line):
            if line.strip() and not line.strip().startswith('"'):
                break
    indent = "  "
    if kept:
        m = re.match(r"^(\s*)", kept[-1])
        if m and m.group(1):
            indent = m.group(1)
    kept.append(f"{indent}sorry")
    return "\n".join(kept)


def _original_sorry_block(
    name: str,
    lemma_text: str,
    stmt_by_name: Dict[str, str],
) -> str:
    stmt = stmt_by_name.get(name, "").strip()
    if stmt and lemma_still_sorry(stmt):
        return stmt
    current = lemma_block_text(lemma_text, name)
    if current:
        return _block_with_sorry_proof(current)
    if stmt:
        return _block_with_sorry_proof(stmt)
    return ""


def _reset_non_sorry_lemmas_to_sorry(
    lemma_thy: Path,
    lemma_text: str,
    names: set[str],
    stmt_by_name: Dict[str, str],
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> str:
    """将引理块中一切非 sorry 占位恢复为 sorry，避免错误证明污染后续验证。"""
    updated = lemma_text
    for name in sorted(names):
        block = lemma_block_text(updated, name)
        if not block or lemma_still_sorry(block):
            continue
        original = _original_sorry_block(name, updated, stmt_by_name)
        if not original.strip():
            continue
        reset_lemma_to_sorry(
            lemma_thy,
            name,
            original,
            server_pool=server_pool,
        )
        updated = lemma_thy.read_text(encoding="utf-8")
    return updated


def _all_used_lemmas_verified(
    unproven_text: str,
    usage: TheoremLemmaUsageReport,
) -> bool:
    used_names = _used_lemma_names(usage)
    if not used_names:
        return True
    for name in used_names:
        if not _lemma_block_verified(unproven_text, name):
            return False
    return True


@dataclass
class UsedLemmaProofResult:
    theorem_name: str
    thy_path: str
    unproven_lemmas_path: str = ""
    usage_report: Dict[str, Any] = field(default_factory=dict)
    lemmas_attempted: int = 0
    lemmas_proved: int = 0
    lemma_results: List[Dict[str, Any]] = field(default_factory=list)
    final_theorem_verified: bool = False
    final_all_used_lemmas_verified: bool = False
    final_all_unproven_lemmas_verified: bool = False
    lemma_proof_prompt_path: str = ""
    stopped_early: bool = False
    """主定理引用的引理证明失败时提前终止。"""
    fail_fast_lemma: str = ""
    """触发失败即停的引理名（若有）。"""

    def to_dict(self) -> dict:
        return {
            "theorem_name": self.theorem_name,
            "thy_path": self.thy_path,
            "unproven_lemmas_path": self.unproven_lemmas_path,
            "usage_report": self.usage_report,
            "lemmas_attempted": self.lemmas_attempted,
            "lemmas_proved": self.lemmas_proved,
            "lemma_results": self.lemma_results,
            "final_theorem_verified": self.final_theorem_verified,
            "final_all_used_lemmas_verified": self.final_all_used_lemmas_verified,
            "final_all_unproven_lemmas_verified": self.final_all_unproven_lemmas_verified,
            "lemma_proof_prompt_path": self.lemma_proof_prompt_path,
            "stopped_early": self.stopped_early,
            "fail_fast_lemma": self.fail_fast_lemma,
        }


def _success_applied_proof(record: Dict[str, Any]) -> str:
    for att in reversed(record.get("attempts") or []):
        if att.get("success") and att.get("applied_proof"):
            return str(att["applied_proof"]).strip()
    return ""


def _reapply_successful_lemma_proofs(
    lemma_thy: Path,
    lemma_results: List[Dict[str, Any]],
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> None:
    """unused 引理逐条证明时会重置其它 unused 为 sorry；结束时恢复全部已成功证明。"""
    from .iterator import apply_lemma_proof_to_thy

    text = lemma_thy.read_text(encoding="utf-8")
    changed = False
    for rec in lemma_results:
        if not rec.get("success"):
            continue
        name = str(rec.get("lemma_name") or "")
        proof = _success_applied_proof(rec)
        if not name or not proof:
            continue
        block = lemma_block_text(text, name)
        if block and not lemma_still_sorry(block):
            continue
        try:
            apply_lemma_proof_to_thy(
                lemma_thy, name, proof, server_pool=server_pool
            )
            changed = True
            text = lemma_thy.read_text(encoding="utf-8")
        except Exception as exc:
            logger.warning("重新写入引理 %s 证明失败: %s", name, exc)
    if changed:
        print(
            "[lemma_proving] 已恢复本轮全部成功引理证明（避免 unused 互斥重置丢失）",
            flush=True,
        )


def prove_used_lemmas_after_theorem(
    sketch_thy_path: Path,
    usage: TheoremLemmaUsageReport,
    isabelle_config: IsabelleRunnerConfig,
    lemma_proof_iterator: LemmaProofIterator,
    lemma_cache: Optional[LemmaCache] = None,
    *,
    unproven_lemmas_path: Optional[Path] = None,
    domain: str = "priority_queue",
    server_pool: Optional[IsabelleServerSessionPool] = None,
    light_lemma_verify: bool = False,
) -> UsedLemmaProofResult:
    """
    在 unproven_lemmas.thy 上对 sorry 引理迭代证明。

    - 主定理引用的引理（used）：失败即停，不再证明后续引理。
    - 未被主定理引用的引理（unused）：证明前清理其它未验证引理为 sorry；
      单条失败后恢复 sorry 并继续下一条。
    - 主定理引用的引理全部通过后，再对 sketch.thy 做整体验证。
    """
    lemma_thy = unproven_lemmas_path or sketch_thy_path
    lemma_text = lemma_thy.read_text(encoding="utf-8")
    stmt_by_name = _stmt_by_name_from_usage(usage)
    used_names = _used_lemma_names(usage)
    all_blocks = lemma_blocks_in_thy(lemma_text)
    unused_names = set(all_blocks.keys()) - used_names

    # 启动前：unused 中非 sorry 的引理一律恢复 sorry，清除僵尸错误证明
    lemma_text = _reset_non_sorry_lemmas_to_sorry(
        lemma_thy,
        lemma_text,
        unused_names,
        stmt_by_name,
        server_pool=server_pool,
    )
    # 启动前：used 中非 sorry 的引理恢复 sorry，确保进入待证队列
    lemma_text = _reset_non_sorry_lemmas_to_sorry(
        lemma_thy,
        lemma_text,
        used_names,
        stmt_by_name,
        server_pool=server_pool,
    )

    targets = _sorry_targets_from_unproven(lemma_text, usage)
    used_targets, unused_targets = _split_sorry_targets(targets, usage)
    ordered_targets = used_targets + unused_targets

    result = UsedLemmaProofResult(
        theorem_name=usage.theorem_name,
        thy_path=str(sketch_thy_path),
        unproven_lemmas_path=str(lemma_thy),
        usage_report=usage.to_dict(),
        lemmas_attempted=len(ordered_targets),
        lemma_proof_prompt_path=lemma_proof_iterator._prompt_path,
    )

    n_external = len(usage.external_refs)
    n_unproven_total = len(all_blocks)
    print(
        f"\n[lemma_proving] 主定理已暂时验证；"
        f"unproven 共 {n_unproven_total} 条引理，待证 {len(ordered_targets)} 条 "
        f"(主定理引用 {len(used_targets)} 条失败即停，"
        f"未引用 {len(unused_targets)} 条失败恢复 sorry 继续)，"
        f"首次≤{lemma_proof_iterator.config.used_lemma_initial_max_attempts}，"
        f"修复≤{lemma_proof_iterator.config.used_lemma_repair_max_attempts}/轮首次，"
        f"外部引用（不证）{n_external} 条",
        flush=True,
    )

    def _record_success(entry: LemmaUsageEntry) -> None:
        nonlocal lemma_text
        lemma_text = lemma_thy.read_text(encoding="utf-8")
        result.lemmas_proved += 1
        if not lemma_cache or not entry.statement.strip():
            return
        proof_block = lemma_block_text(lemma_text, entry.name)
        lemma = Lemma(
            statement=entry.statement,
            proof=proof_block,
            status="verified",
            metadata={
                "theorem": usage.theorem_name,
                "role": "unproven_lemma",
                "proof_source": "lemma_proving",
            },
        )
        lemma.mark_verified()
        if not lemma_cache.add(lemma):
            lemma_cache.update(
                entry.statement,
                {
                    "status": "verified",
                    "proof": lemma.proof,
                    "metadata": lemma.metadata,
                },
            )

    for entry in ordered_targets:
        is_used = entry.name in used_names
        if not is_used:
            # 方案 4：证 unused 前，清理其它非 sorry 的 unused 引理
            lemma_text = _reset_non_sorry_lemmas_to_sorry(
                lemma_thy,
                lemma_text,
                unused_names - {entry.name},
                stmt_by_name,
                server_pool=server_pool,
            )

        original_block = (
            _original_sorry_block(entry.name, lemma_text, stmt_by_name)
            or entry.statement
        )
        role = "主定理引用" if is_used else "未引用"
        print(f"  → {entry.name} ({role})", flush=True)
        one = lemma_proof_iterator.prove_one_lemma(
            lemma_thy,
            entry.name,
            original_block,
            isabelle_config,
            context_thy_path=DefinitionStore.defs_thy_path(
                lemma_proof_iterator.config.output_dir,
                domain,
            ),
            proven_lemmas_path=ProvenLemmaStore.proven_thy_path(
                lemma_proof_iterator.config.output_dir,
                domain,
            ),
            max_initial=(
                lemma_proof_iterator.config.used_lemma_initial_max_attempts
                if is_used
                else 1
            ),
            max_repair=(
                lemma_proof_iterator.config.used_lemma_repair_max_attempts
                if is_used
                else 1
            ),
            server_pool=server_pool,
            light_verify=light_lemma_verify,
        )
        result.lemma_results.append(one)
        print(f"    [lemma_proving] {summarize_lemma_proof_result(one)}", flush=True)
        lemma_text = lemma_thy.read_text(encoding="utf-8")

        if one.get("success"):
            _record_success(entry)
            continue

        if is_used:
            # 方案 3：主定理引用的引理失败即停
            result.stopped_early = True
            result.fail_fast_lemma = entry.name
            print(
                f"[lemma_proving] 主定理引用引理 {entry.name} 证明失败，"
                f"停止后续引理证明",
                flush=True,
            )
            break

        # 方案 4：unused 失败，恢复 sorry 后继续
        reset_lemma_to_sorry(
            lemma_thy,
            entry.name,
            original_block,
            server_pool=server_pool,
        )
        lemma_text = lemma_thy.read_text(encoding="utf-8")
        print(
            f"    [lemma_proving] {entry.name} 未验证通过，已恢复 sorry，继续下一条",
            flush=True,
        )

    _reapply_successful_lemma_proofs(
        lemma_thy, result.lemma_results, server_pool=server_pool
    )
    lemma_text = lemma_thy.read_text(encoding="utf-8")
    used_ok = (
        not result.stopped_early
        and _all_used_lemmas_verified(lemma_text, usage)
    )
    all_ok = _all_unproven_lemmas_satisfied(lemma_text)
    result.final_all_used_lemmas_verified = used_ok
    result.final_all_unproven_lemmas_verified = all_ok
    print(
        f"[lemma_proving] 完成 {result.lemmas_proved}/{result.lemmas_attempted}；"
        f"主定理引用引理: {'通过' if used_ok else '未通过'}；"
        f"unproven 全部引理: {'通过' if all_ok else '未通过'}",
        flush=True,
    )
    if used_ok and sketch_thy_path.is_file():
        print(
            "[lemma_proving] 主定理引用引理已全部通过，重新验证 sketch ...",
            flush=True,
        )
        sketch_ok, _ = verify_then_sledgehammer(
            sketch_thy_path,
            isabelle_config,
            server_pool=server_pool,
        )
        result.final_theorem_verified = sketch_ok
        print(
            f"[lemma_proving] sketch 重验证: {'通过' if sketch_ok else '未通过'}",
            flush=True,
        )
    return result


def light_verify_unproven_lemmas(
    unproven_path: Path,
    lemma_names: List[str],
    isabelle_config: IsabelleRunnerConfig,
    *,
    server_pool: Optional[IsabelleServerSessionPool] = None,
) -> Tuple[bool, List[Dict[str, Any]]]:
    """
    对已有证明、待 Isabelle 确认的引理做切片轻量验证（不重启 session、不加载整份 unproven）。
    """
    results: List[Dict[str, Any]] = []
    all_ok = True
    for i, name in enumerate(lemma_names):
        if server_pool is not None and server_pool.is_active and i > 0:
            prepare_session_for_lemma_proof_verify(server_pool)
        print(f"  → {name} (light verify)", flush=True)
        try:
            ok, out = verify_single_lemma_light(
                unproven_path, name, isabelle_config, server_pool=server_pool
            )
        except ValueError as exc:
            ok, out = False, str(exc)
        rec = {
            "lemma_name": name,
            "success": ok,
            "prompt_kind": "light_verify",
        }
        if not ok and out:
            rec["isabelle_error_preview"] = out[:1500]
            rec["last_error"] = out
        results.append(rec)
        print(f"    [lemma-light] {summarize_light_verify_result(rec)}", flush=True)
        if not ok:
            all_ok = False
    return all_ok, results


def summarize_light_verify_result(record: Dict[str, Any]) -> str:
    name = str(record.get("lemma_name") or "?")
    if record.get("success"):
        return f"{name} 切片验证通过"
    preview = str(record.get("isabelle_error_preview") or record.get("last_error") or "")
    if preview:
        return f"{name} 切片验证失败: {preview[:200]}"
    return f"{name} 切片验证失败"
