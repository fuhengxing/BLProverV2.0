"""
维度 1：引理语法复杂度（prop_nodes）。

在 Isabelle 服务器模式下加载上下文 .thy，对 Thm.prop_of 使用 Term.size_of_term 统计节点数。
整次评估只启动一个 server / session，一次 use_theories 批量输出所有 STATS 行（条数不限）。
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, TYPE_CHECKING

if TYPE_CHECKING:
    from ...utils.isabelle_sledgehammer import IsabelleServerSessionPool

from ...utils.isabelle_sledgehammer import _clamp_isabelle_wait

INLINE_LEMMA_PREFIX = "__eval_target"

LEMMA_HEAD_RE = re.compile(
    r"^\s*(lemma|theorem|corollary)\s+([A-Za-z0-9_']+)",
    re.IGNORECASE,
)
_DECL_START_RE = re.compile(
    r"^\s*(lemma|theorem|corollary|definition|fun|primrec|typedef|locale|type_synonym)\b",
    re.IGNORECASE,
)
_PROOF_START_RE = re.compile(
    r"^\s*(proof\b|apply\b|by\s|oops\b)",
    re.IGNORECASE,
)
STATS_LINE_RE = re.compile(r"STATS\|([^|]+)\|(\d+)\|(\d+)\|(\d+)\|(\d+)\s*$")
STATS_LINE_LEGACY_RE = re.compile(r"STATS\|([^|]+)\|(\d+)\s*$")
SYNTAX_WEIGHTS = {"nodes": 1, "depth": 2, "quant_conn": 2, "var_count": 1}
"""论文 3.1.3：S(i) = 1*节点总数 + 2*树深度 + 2*量词与连接词数 + 1*变量数。"""


@dataclass
class LemmaStats:
    short_name: str
    kind: str
    prop_nodes: int
    source: str
    depth: int = 0
    quant_conn: int = 0
    var_count: int = 0

    def weighted_s(self) -> int:
        """论文 3.1.3 综合语法复杂度 S(i)（四子维度加权求和）。"""
        return (
            SYNTAX_WEIGHTS["nodes"] * int(self.prop_nodes)
            + SYNTAX_WEIGHTS["depth"] * int(self.depth)
            + SYNTAX_WEIGHTS["quant_conn"] * int(self.quant_conn)
            + SYNTAX_WEIGHTS["var_count"] * int(self.var_count)
        )


@dataclass
class BatchAnalysisItem:
    """单条待分析引理（item_id 由调用方指定，如 step1_construct_lemmas1#3）。"""

    item_id: str
    statement: str
    inline_name: Optional[str] = None


@dataclass
class _ResolvedTarget:
    item_id: str
    lemma_name: str
    kind: str
    inject_block: Optional[str]
    preview: str


def _to_cygwin_path(path: str) -> str:
    path_str = str(path).replace("\\", "/")
    if len(path_str) > 1 and path_str[1] == ":":
        drive = path_str[0].lower()
        path_str = f"/cygdrive/{drive}{path_str[2:]}"
    return path_str


def _lemma_declared_in_text(text: str, lemma_name: str) -> bool:
    pat = re.compile(
        rf"^\s*(?:lemma|theorem|corollary)\s+{re.escape(lemma_name)}\b",
        re.IGNORECASE | re.MULTILINE,
    )
    return bool(pat.search(text))


def _insert_before_theory_end(text: str, chunk: str) -> str:
    chunk = chunk.strip("\n") + "\n"
    end_pos = text.rfind("\nend\n")
    if end_pos < 0:
        return text.rstrip() + "\n\n" + chunk + "\nend\n"
    return text[:end_pos] + "\n\n" + chunk + "\n" + text[end_pos:]


def _build_snapshot_base(src_text: str, theory_name: str) -> Tuple[str, str]:
    lines = src_text.splitlines()
    out: List[str] = []
    i = 0
    inserted_qad = False

    while i < len(lines):
        line = lines[i]
        if (not inserted_qad) and line.strip() == "begin":
            out.append(line)
            if "quick_and_dirty" not in src_text:
                out.append("")
                out.append("declare [[quick_and_dirty = true]]")
            inserted_qad = True
            i += 1
            continue

        if LEMMA_HEAD_RE.match(line):
            out.append(line)
            i += 1
            has_sorry = False
            while i < len(lines):
                cur = lines[i]
                if LEMMA_HEAD_RE.match(cur) or cur.strip() == "end":
                    break
                if _DECL_START_RE.match(cur) and not LEMMA_HEAD_RE.match(cur):
                    break
                if _PROOF_START_RE.match(cur):
                    break
                if cur.strip() == "sorry" or cur.strip().endswith(" sorry"):
                    has_sorry = True
                    out.append(cur)
                    i += 1
                    break
                out.append(cur)
                i += 1
            if not has_sorry:
                out.append("  sorry")
            while i < len(lines):
                cur = lines[i]
                if LEMMA_HEAD_RE.match(cur) or cur.strip() == "end":
                    break
                if _DECL_START_RE.match(cur) and not LEMMA_HEAD_RE.match(cur):
                    break
                i += 1
            continue

        out.append(line)
        i += 1

    text = "\n".join(out) + "\n"
    snapshot_theory = f"{theory_name}_stats_snapshot"
    text = re.sub(
        rf'^\s*theory\s+"?{re.escape(theory_name)}"?',
        f'theory "{snapshot_theory}"',
        text,
        count=1,
        flags=re.MULTILINE,
    )
    return text, snapshot_theory


def _make_batch_analysis_snapshot(
    src_text: str,
    theory_name: str,
    lemma_names: List[str],
    inject_by_name: Dict[str, str],
) -> Tuple[str, str]:
    text, snapshot_theory = _build_snapshot_base(src_text, theory_name)
    seen_inject: set[str] = set()
    seen_ml: set[str] = set()
    ml_emit_lines: List[str] = []

    for name in lemma_names:
        if name in inject_by_name and name not in seen_inject:
            if not _lemma_declared_in_text(text, name):
                block = inject_by_name[name].strip("\n")
                if not any(ln.strip() == "sorry" for ln in block.splitlines()):
                    block += "\n  sorry"
                text = _insert_before_theory_end(text, block)
            seen_inject.add(name)

        if name in seen_ml:
            continue
        seen_ml.add(name)
        ml_emit_lines.append("  yb_emit " + _ml_string_literal(name) + " @{thm " + name + "};")

    if ml_emit_lines:
        ml_block = _syntax_stats_ml_block(ml_emit_lines)
        text = _insert_before_theory_end(text, ml_block)

    return text, snapshot_theory


def _ml_string_literal(value: str) -> str:
    return '"' + str(value).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _syntax_stats_ml_block(emit_lines: List[str]) -> str:
    """
    论文 3.1.3：一次性注入的 Isabelle/ML 探针，对若干定理命题统计
    节点总数 / 树深度 / 量词与连接词数 / 变量数，并输出 STATS 行。
    """
    prologue = [
        "ML {*",
        "  fun yb_at (Const _) = true | yb_at (Free _) = true | yb_at (Var _) = true",
        "        | yb_at (Bound _) = true | yb_at _ = false;",
        "  fun yb_args (f $ u) = u :: yb_args f | yb_args _ = [];",
        "  fun yb_nodes t = if yb_at t then 1 else",
        "    (case t of Abs (_, _, b) => 1 + yb_nodes b",
        "      | (f $ _) => 1 + List.foldl (op +) 0 (map yb_nodes (yb_args t)));",
        "  fun yb_depth t = if yb_at t then 0 else",
        "    (case t of Abs (_, _, b) => 1 + yb_depth b",
        "      | (f $ _) => 1 + List.foldl Int.max 0 (map yb_depth (yb_args t)));",
        "  fun yb_vars t = if yb_at t then",
        "    (case t of Free (x, _) => [x] | Var (xi, _) => [Term.string_of_vname xi] | _ => [])",
        "    else (case t of Abs (x, _, b) => x :: yb_vars b",
        "      | (f $ _) => List.concat (map yb_vars (yb_args t)));",
        "  fun yb_qc t = if yb_at t then",
        "    (case t of Const (n, _) =>",
        "       (if List.exists (fn s => String.isSuffix s n)",
        '          ["HOL.All", "HOL.Ex", "HOL.conj", "HOL.disj", "HOL.implies", "Pure.all", "Pure.imp"]',
        "        then 1 else 0) | _ => 0)",
        "    else (case t of Abs (_, _, b) => yb_qc b",
        "      | (f $ _) => List.foldl (op +) 0 (map yb_qc (yb_args t)));",
        "  fun yb_distinct (x, acc) = if List.exists (fn y => x = y) acc then acc else x :: acc;",
        "  fun yb_emit name th =",
        "    let val (n, d, q, v) =",
        "      (yb_nodes (Thm.prop_of th), yb_depth (Thm.prop_of th),",
        "       yb_qc (Thm.prop_of th),",
        "       List.length (List.foldl yb_distinct [] (yb_vars (Thm.prop_of th))))",
        '    in writeln ("STATS|" ^ name ^ "|" ^ Int.toString n ^ "|" ^ Int.toString d',
        '      ^ "|" ^ Int.toString q ^ "|" ^ Int.toString v) end;',
    ]
    return "\n".join(prologue + emit_lines + ["*}"])


def _parse_lemma_from_block(block: str) -> Tuple[str, str, str]:
    preview = block.replace("\n", " ").strip()
    if len(preview) > 120:
        preview = preview[:117] + "..."
    for line in block.splitlines():
        m = LEMMA_HEAD_RE.match(line.strip())
        if m:
            return m.group(1).lower(), m.group(2), preview
    return "lemma", INLINE_LEMMA_PREFIX, preview


def normalize_statement_block(
    statement: str,
    inline_name: Optional[str] = None,
) -> Tuple[str, str, str, str]:
    block = statement.strip("\n")
    kind, name, preview = _parse_lemma_from_block(block)
    target_name = inline_name or name
    if name == INLINE_LEMMA_PREFIX and inline_name:
        name = inline_name
    if not LEMMA_HEAD_RE.match(block.splitlines()[0].strip() if block.splitlines() else ""):
        inject = f"lemma {target_name}:\n  {block}\n"
        return target_name, "lemma", inject, preview
    inject = block if block.rstrip().endswith("sorry") else block + "\n  sorry\n"
    return name, kind, inject, preview


def _resolve_targets(
    thy_text: str, items: List[BatchAnalysisItem]
) -> List[_ResolvedTarget]:
    resolved: List[_ResolvedTarget] = []
    for item in items:
        text = (item.statement or "").strip()
        if not text:
            continue
        name, kind, inject, preview = normalize_statement_block(
            text, inline_name=item.inline_name
        )
        if _lemma_declared_in_text(thy_text, name):
            inject = None
        resolved.append(
            _ResolvedTarget(
                item_id=item.item_id,
                lemma_name=name,
                kind=kind,
                inject_block=inject,
                preview=preview,
            )
        )
    return resolved


def _batch_watchdog_timeout(per_item_timeout: int, count: int) -> int:
    if count <= 0:
        return _clamp_isabelle_wait(per_item_timeout)
    scaled = max(per_item_timeout, 90 + 12 * count)
    return _clamp_isabelle_wait(scaled)


def _extract_session_id(start_responses) -> Optional[str]:
    if isinstance(start_responses, str):
        return start_responses
    if isinstance(start_responses, list):
        for item in reversed(start_responses):
            body = getattr(item, "response_body", None)
            sid = getattr(body, "session_id", None)
            if sid:
                return str(sid)
    return None


def _collect_messages_from_responses(responses) -> List[str]:
    messages: List[str] = []
    for resp in responses or []:
        rvalue = getattr(getattr(resp, "response_type", ""), "value", None) or str(
            getattr(resp, "response_type", "")
        )
        if str(rvalue).upper() != "FINISHED":
            continue
        body = getattr(resp, "response_body", None)
        data = body.model_dump() if hasattr(body, "model_dump") else {}
        for node in data.get("nodes", []) or []:
            for msg in node.get("messages", []) or []:
                if msg.get("kind") in {"writeln", "warning", "error"}:
                    messages.append(str(msg.get("message", "")))
    return messages


def _parse_all_stats_from_messages(
    messages: List[str],
) -> Dict[str, Tuple[int, int, int, int]]:
    """解析 STATS|<name>|<nodes>|<depth>|<quant+conn>|<vars>（兼容旧的两段格式）。"""
    out: Dict[str, Tuple[int, int, int, int]] = {}
    for msg in messages:
        for line in msg.splitlines():
            stripped = line.strip()
            m = STATS_LINE_RE.search(stripped)
            if m:
                out[m.group(1)] = (
                    int(m.group(2)),
                    int(m.group(3)),
                    int(m.group(4)),
                    int(m.group(5)),
                )
                continue
            legacy = STATS_LINE_LEGACY_RE.search(stripped)
            if legacy:
                out[legacy.group(1)] = (int(legacy.group(2)), 0, 0, 0)
    return out


def analyze_statements_batch(
    thy_path: Path,
    items: List[BatchAnalysisItem],
    timeout: int = 60,
    server_pool: Optional["IsabelleServerSessionPool"] = None,
) -> Dict[str, Tuple[Optional[LemmaStats], str]]:
    empty: Dict[str, Tuple[Optional[LemmaStats], str]] = {}
    if not items:
        return empty

    try:
        import nest_asyncio
        from isabelle_client import get_isabelle_client, start_isabelle_server
    except ImportError as exc:
        err = f"缺少依赖: {exc}（请 pip install isabelle-client nest-asyncio）"
        return {it.item_id: (None, err) for it in items if (it.statement or "").strip()}

    thy_text = thy_path.read_text(encoding="utf-8")
    targets = _resolve_targets(thy_text, items)
    if not targets:
        return empty

    theory_name = thy_path.stem
    inject_by_name: Dict[str, str] = {}
    ordered_names: List[str] = []
    seen_names: set[str] = set()
    for t in targets:
        if t.lemma_name not in seen_names:
            ordered_names.append(t.lemma_name)
            seen_names.add(t.lemma_name)
        if t.inject_block:
            inject_by_name[t.lemma_name] = t.inject_block

    snapshot_text, snapshot_theory = _make_batch_analysis_snapshot(
        thy_text, theory_name, ordered_names, inject_by_name
    )
    snapshot_path = thy_path.parent / f"{snapshot_theory}.thy"
    snapshot_path.write_text(snapshot_text, encoding="utf-8", newline="\n")

    watchdog = _batch_watchdog_timeout(timeout, len(ordered_names))
    theory_dir = thy_path.parent
    try:
        rel = theory_dir.relative_to(Path.cwd())
        master_dir = str(rel).replace("\\", "/") or "."
    except ValueError:
        master_dir = _to_cygwin_path(str(theory_dir.absolute()))

    use_pool = server_pool is not None and getattr(server_pool, "_active", False)
    server_entry = None
    client = None
    session_id = None
    server_proc = None

    try:
        if use_pool:
            responses = server_pool.use_theories(
                theories=[snapshot_theory],
                master_dir=master_dir,
                watchdog_timeout=watchdog,
            )
        else:
            try:
                import nest_asyncio
                from isabelle_client import get_isabelle_client, start_isabelle_server
            except ImportError as exc:
                err = f"缺少依赖: {exc}（请 pip install isabelle-client nest-asyncio）"
                return {it.item_id: (None, err) for it in items if (it.statement or "").strip()}

            nest_asyncio.apply()
            from ...utils.isabelle_server_lifecycle import (
                close_ephemeral_server,
                register_ephemeral_server,
            )

            server_info, server_proc = start_isabelle_server()
            client = get_isabelle_client(server_info)
            server_entry = register_ephemeral_server(client, None, server_proc)
            session_id = _extract_session_id(client.session_start())
            server_entry["session_id"] = session_id
            if not session_id:
                err = "无法获取 Isabelle server session_id"
                return {t.item_id: (None, err) for t in targets}

            responses = client.use_theories(
                theories=[snapshot_theory],
                master_dir=master_dir,
                session_id=session_id,
                watchdog_timeout=watchdog,
            )

        messages = _collect_messages_from_responses(responses)
        log = "\n".join(messages)
        stats_map = _parse_all_stats_from_messages(messages)

        results: Dict[str, Tuple[Optional[LemmaStats], str]] = {}
        for t in targets:
            stats = stats_map.get(t.lemma_name)
            if stats is not None:
                nodes, depth, quant_conn, var_count = stats
                results[t.item_id] = (
                    LemmaStats(
                        short_name=t.lemma_name,
                        kind=t.kind,
                        prop_nodes=nodes,
                        source="isabelle_server/yb_syntax_stats",
                        depth=depth,
                        quant_conn=quant_conn,
                        var_count=var_count,
                    ),
                    log,
                )
            else:
                results[t.item_id] = (
                    None,
                    f"未找到 STATS|{t.lemma_name}|；"
                    f"已解析: {sorted(stats_map.keys())}\n{log[-1500:]}",
                )
        return results
    except Exception as exc:
        err = f"服务器模式异常: {exc}"
        return {t.item_id: (None, err) for t in targets}
    finally:
        if server_entry is not None:
            from ...utils.isabelle_server_lifecycle import close_ephemeral_server

            close_ephemeral_server(server_entry)
        if snapshot_path.exists():
            snapshot_path.unlink()


def analyze_statement(
    thy_path: Path,
    statement: str,
    timeout: int = 60,
    inline_name: Optional[str] = None,
) -> Tuple[Optional[LemmaStats], str]:
    item_id = inline_name or "__single"
    results = analyze_statements_batch(
        thy_path,
        [BatchAnalysisItem(item_id=item_id, statement=statement, inline_name=inline_name)],
        timeout=timeout,
    )
    return results.get(item_id, (None, "未执行分析"))
