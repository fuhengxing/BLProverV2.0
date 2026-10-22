"""
基于引理的草图生成器
生成Isabelle证明草图，使用引理分解复杂证明
"""

import re
import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from ..llm.base import LLMInterface
from ..lemma import LemmaCache, MatchType
from ..utils.isabelle_parser import IsabelleParser
from .construct_lemma_generator import (
    format_function_definitions_block,
    format_theorem_statement_block,
)

logger = logging.getLogger(__name__)

_SKETCH_TASK_SPLIT = re.compile(
    r"####\s*below\s+are\s+your\s+task",
    re.IGNORECASE,
)
_USER_PROVIDE_SKETCH = "{{user provide}}"


class SketchGenerator:
    """基于引理的草图生成器"""
    
    def __init__(
        self,
        llm: LLMInterface,
        lemma_cache: Optional[LemmaCache] = None,
        sketch_prompt_path: Optional[str] = None,
    ):
        """
        初始化草图生成器
        
        Args:
            llm: LLM接口
            lemma_cache: 引理缓存（可选）
            sketch_prompt_path: sketch prompt.txt 路径；缺省或文件无效时使用内置英文提示
        """
        self.llm = llm
        self.lemma_cache = lemma_cache
        self.parser = IsabelleParser()
        self._sketch_file_prompt: Optional[Tuple[str, str]] = None
        if sketch_prompt_path:
            p = Path(sketch_prompt_path)
            if p.is_file():
                raw = p.read_text(encoding="utf-8")
                m = _SKETCH_TASK_SPLIT.search(raw)
                if m:
                    self._sketch_file_prompt = (
                        raw[: m.start()].strip(),
                        raw[m.start() :].strip(),
                    )
                    logger.info("已加载草图提示词文件: %s", p)
                else:
                    logger.warning(
                        "草图提示词中未找到锚点 ####below are your task，将使用内置草图提示"
                    )
            else:
                logger.warning("sketch_prompt_path 不存在 (%s)，将使用内置草图提示", p)
    
    def format_merged_lemmas_for_sketch(
        self, lemma_concepts: List[Dict[str, str]]
    ) -> str:
        """与草图 user 模板第四段一致，供落盘 lemmas_for_sketch.txt。"""
        return self._format_potentially_useful_lemmas(lemma_concepts)

    def generate_sketch(
        self,
        theorem_data: Dict,
        informal_proof: Optional[str] = None,
        lemma_concepts: Optional[List[Dict[str, str]]] = None,
        constructed_lemma_concepts: Optional[List[Dict[str, str]]] = None,
        isabelle_error: Optional[str] = None,
        previous_sketch: Optional[str] = None,
        iteration: int = 1,
        sketch_prompt_blocks: Optional[Dict[str, str]] = None,
    ) -> str:
        """
        生成基于引理的证明草图
        
        Args:
            theorem_data: 定理数据，包含：
                - "theorem name": 定理名称
                - "formal theorem statement": 形式化定理陈述
                - "formal function definitions": 函数定义（可选）
            informal_proof: 自然语言证明（可选）
            lemma_concepts: 引理概念列表（可选，若提供则直接使用，忽略合并逻辑）
            constructed_lemma_concepts: 构造引理阶段得到的引理（可选）；为 None 且 lemma_concepts 为 None 时仅走已验证库检索
            
        Returns:
            str: Isabelle证明草图
        """
        theorem_name = theorem_data.get("theorem name", "theorem")
        formal_statement = theorem_data.get("formal theorem statement", "")
        func_defs = theorem_data.get("formal function definitions", {})
        
        logger.info(f"生成证明草图: {theorem_name}")
        
        if lemma_concepts is None:
            lemma_concepts = self.build_merged_lemma_concepts(
                theorem_data,
                informal_proof,
                constructed_lemma_concepts,
            )
        
        # 生成草图
        sketch = self._generate_sketch_with_lemmas(
            theorem_data,
            theorem_name,
            formal_statement,
            func_defs,
            informal_proof,
            lemma_concepts,
            isabelle_error=isabelle_error,
            previous_sketch=previous_sketch,
            iteration=iteration,
            sketch_prompt_blocks=sketch_prompt_blocks,
        )
        
        return sketch
    
    def _concept_description(self, item: Dict[str, str]) -> str:
        return (item.get("description") or item.get("statement") or "").strip()

    def build_merged_lemma_concepts(
        self,
        theorem_data: Dict,
        informal_proof: Optional[str],
        constructed_lemma_concepts: Optional[List[Dict[str, str]]],
    ) -> List[Dict[str, str]]:
        """
        与 generate_sketch 内部一致：构造引理 + 已验证库 Top-5，供 main 落盘与草图共用。
        """
        formal_statement = theorem_data.get("formal theorem statement", "")
        return self._merge_lemma_concepts(
            formal_statement,
            informal_proof,
            constructed_lemma_concepts,
        )

    def _merge_lemma_concepts(
        self,
        formal_statement: str,
        informal_proof: Optional[str],
        constructed_lemma_concepts: Optional[List[Dict[str, str]]],
    ) -> List[Dict[str, str]]:
        """
        先加入本轮构造的全部 new lemma，再追加已验证库向量检索 Top-5（按陈述去重）。
        """
        merged: List[Dict[str, str]] = []
        seen_norm = set()

        def add_concept(
            name: str,
            desc: str,
            meaning: str = "",
            source: str = "",
        ) -> None:
            d = desc.strip()
            if not d:
                return
            key = self.parser.normalize_statement(d)
            if key in seen_norm:
                return
            seen_norm.add(key)
            merged.append(
                {
                    "name": name,
                    "description": d,
                    "meaning": (meaning or "").strip(),
                    "source": (source or "").strip(),
                }
            )

        if constructed_lemma_concepts:
            for item in constructed_lemma_concepts:
                desc = self._concept_description(item)
                if not desc:
                    continue
                nm = (item.get("name") or f"constructed_lemma_{len(merged) + 1}").strip()
                meaning = (item.get("meaning") or "").strip()
                source = (item.get("source") or "").strip()
                add_concept(nm, desc, meaning, source)

        n_constructed = len(merged)

        if self.lemma_cache:
            try:
                top_k = 5
                hits = self.lemma_cache.find_all(
                    formal_statement,
                    match_types=[MatchType.SIMILARITY],
                )[:top_k]
                for i, (lemma, _match_type, _score) in enumerate(hits, start=1):
                    nm = f"cached_lemma_{i}"
                    add_concept(
                        nm,
                        lemma.statement,
                        meaning=f"Candidate lemma `{nm}` retrieved from verified lemma library.",
                        source=f"Verified lemma library similarity retrieval (top-{top_k}).",
                    )
            except Exception as e:
                logger.warning(f"从引理库检索候选引理失败: {e}")

        if n_constructed:
            logger.info(
                "草图引理提示: 构造引理 %d 条，合并后共 %d 条",
                n_constructed,
                len(merged),
            )
        elif merged:
            logger.info(f"从引理库检索到 {len(merged)} 个候选引理用于辅助生成草图")

        return merged

    def _format_potentially_useful_lemmas(self, lemma_concepts: List[Dict[str, str]]) -> str:
        """与 sketch prompt few-shot 中 potentially useful lemmas 段风格一致。"""
        if not lemma_concepts:
            return "(none)"
        lines: List[str] = []
        for i, lem in enumerate(lemma_concepts, 1):
            name = (lem.get("name") or f"lemma_{i}").strip()
            desc = self._concept_description(lem)
            if not desc:
                continue
            meaning_line = (lem.get("meaning") or "").strip()
            source_line = (lem.get("source") or "").strip()
            if not meaning_line:
                meaning_line = f"Candidate lemma `{name}` for this proof."
            if not source_line:
                source_line = (
                    "Verified lemma library similarity retrieval."
                    if name.startswith("cached_lemma")
                    else "Derived from gaps in the step-by-step informal proof."
                )
            lines.append(f"Meaning: {meaning_line}")
            lines.append(f"Source: {source_line}")
            lines.append(f"### new lemma{i}")
            lines.append("```isabelle")
            lines.append(desc)
            lines.append("```")
            lines.append("")
        return "\n".join(lines).strip() or "(none)"

    def _fill_sketch_user_template(
        self,
        user_template: str,
        theorem_data: Dict,
        informal_proof: Optional[str],
        lemma_concepts: List[Dict[str, str]],
        sketch_prompt_blocks: Optional[Dict[str, str]] = None,
    ) -> str:
        if sketch_prompt_blocks is not None:
            b = sketch_prompt_blocks
            replacements = [
                (b.get("function_definitions") or "").strip(),
                (b.get("theorem_statement") or "").strip(),
                (b.get("informal_proof") or "").strip() or "(none)",
                (b.get("lemmas") or "").strip() or "(none)",
            ]
        else:
            replacements = [
                format_function_definitions_block(theorem_data),
                format_theorem_statement_block(theorem_data),
                (informal_proof or "").strip() or "(none)",
                self._format_potentially_useful_lemmas(lemma_concepts),
            ]
        out = user_template
        for block in replacements:
            if _USER_PROVIDE_SKETCH not in out:
                raise ValueError("sketch 用户模板中 {{user provide}} 占位符不足 4 个")
            out = out.replace(_USER_PROVIDE_SKETCH, block, 1)
        return out

    def _generate_sketch_from_file_prompt(
        self,
        theorem_data: Dict,
        informal_proof: Optional[str],
        lemma_concepts: List[Dict[str, str]],
        isabelle_error: Optional[str] = None,
        previous_sketch: Optional[str] = None,
        iteration: int = 1,
        sketch_prompt_blocks: Optional[Dict[str, str]] = None,
    ) -> str:
        assert self._sketch_file_prompt is not None
        base_system, user_template = self._sketch_file_prompt
        system_prompt = base_system
        if iteration > 1:
            system_prompt += """

You are in REPAIR mode. The previous Isabelle theory FAILED verification.
Rules:
1) Do NOT change the theorem statement.
2) Do NOT introduce new imports or external theory dependencies.
3) Prefer minimal edits; keep lemma/theorem names stable when possible.
4) Preserve step comments in (* ... *); prefer by simp/auto/blast and named lemmas; use sledgehammer sparingly (at most 5–8 per theorem, own line only, as in the main instructions).
5) Address the specific failing goal/step indicated by Isabelle. Do NOT output an unchanged sketch.
"""
        user_prompt = self._fill_sketch_user_template(
            user_template,
            theorem_data,
            informal_proof,
            lemma_concepts,
            sketch_prompt_blocks=sketch_prompt_blocks,
        )
        if iteration > 1 and isabelle_error:
            user_prompt += f"""

Isabelle verification FAILED. Here is the error feedback (verbatim):
{isabelle_error}
"""
        if iteration > 1 and previous_sketch:
            user_prompt += f"""

Here is the previous failed theory/sketch. Revise it to fix the error:
{previous_sketch}
"""
        try:
            sketch = self.llm.generate(user_prompt, system_prompt)
            sketch = self._clean_sketch(sketch)
            logger.info(f"生成草图完成，长度: {len(sketch)}")
            return sketch
        except Exception as e:
            logger.error(f"生成草图失败: {e}")
            raise

    def _generate_sketch_with_lemmas(
        self,
        theorem_data: Dict,
        theorem_name: str,
        formal_statement: str,
        func_defs: Dict[str, str],
        informal_proof: Optional[str],
        lemma_concepts: List[Dict[str, str]],
        isabelle_error: Optional[str] = None,
        previous_sketch: Optional[str] = None,
        iteration: int = 1,
        sketch_prompt_blocks: Optional[Dict[str, str]] = None,
    ) -> str:
        """
        使用引理生成草图
        
        Args:
            theorem_data: 完整定理 JSON（用于与 construct 一致的函数定义/定理格式化）
            theorem_name: 定理名称
            formal_statement: 形式化定理陈述
            func_defs: 函数定义
            informal_proof: 自然语言证明
            lemma_concepts: 引理概念列表
            
        Returns:
            str: Isabelle证明草图
        """
        if self._sketch_file_prompt:
            return self._generate_sketch_from_file_prompt(
                theorem_data,
                informal_proof,
                lemma_concepts,
                isabelle_error=isabelle_error,
                previous_sketch=previous_sketch,
                iteration=iteration,
                sketch_prompt_blocks=sketch_prompt_blocks,
            )

        system_prompt = """You are an expert in Isabelle/HOL theorem proving.
Generate a formal proof sketch in Isabelle/Isar syntax that uses lemmas to decompose the problem.

OUTPUT FORMAT (MUST FOLLOW):
- Output ONLY Isabelle/Isar code. Absolutely NO natural-language explanations, no Markdown, no headings.
- Do NOT include phrases like "Here is ..." or "Explanation" or bullet lists.
- Do NOT output any chain-of-thought / reasoning. Only output the final Isabelle code.
- Wrap the code strictly between the two marker lines below, and output nothing else:
  <ISABELLE>
  ... Isabelle code ...
  </ISABELLE>

CRITICAL REQUIREMENTS:
1. Use Isabelle/Isar syntax, NOT Coq syntax!
   - Use "proof -" NOT "Proof."
   - Use "qed" NOT "Qed."
   - Use "by" or "apply" for tactics
   - Use "show" for goals
   - Use "have" for intermediate lemmas

2. ABSOLUTELY NO "sorry" ALLOWED!
   - You MUST provide complete proofs for all lemmas and the main theorem
   - Use actual Isabelle tactics instead of "sorry"
   - If a step is simple, use "by auto", "by simp", or other appropriate tactics
   - If a step requires more work, break it down into smaller steps with "have" statements

3. NEVER use "where" in proof statements!
   - "where" is ONLY for definitions (definition, fun, function), NOT for proofs
   - WRONG: have "(x, y) = f z" where "x = ..." and "y = ..."
   - CORRECT: obtain x y where "(x, y) = f z" by ...
   - CORRECT: have "(x, y) = f z" by ...
   - CORRECT: let ?x = ... in have "..."
   - Use "obtain" to introduce variables with conditions
   - Use "let" for local definitions in proofs

Structure your proof as:
1. Define helper lemmas with COMPLETE proofs (no sorry!)
2. Prove the main theorem using these lemmas with COMPLETE proof steps

Common Isabelle tactics to use:
- by auto, by simp, by blast, by fastforce, by force
- by metis, by meson, by arith
- by (induction xs) auto
- by (cases xs) auto
- unfolding def_name by auto
- by (rule some_rule)
- using lemma_name by auto
- have h: ... using lemma_name by auto
- from lemma_name have h: ... by auto
- show ?thesis using lemma1 lemma2 by auto
- obtain x where "x = ..." by ...
- let ?x = ... in ..."""

        if iteration > 1:
            system_prompt += """

You are in REPAIR mode.
The previous Isabelle theory FAILED verification. Your job is to FIX the proof.
Rules:
1) Do NOT change the theorem statement.
2) Do NOT introduce new external dependencies or new imports.
3) Prefer minimal edits: fix the specific lemma/proof step that the error points to.
4) Keep existing lemma/theorem names stable when possible.
5) Return a complete revised theory snippet (lemmas + theorem) with no 'sorry'.
6) You MUST address the failing goal reported by Isabelle. Do NOT repeat the previous sketch unchanged.
7) If Isabelle reports "Failed to finish proof (line ...)" you MUST rewrite that lemma/theorem proof so that it finishes.
"""
        
        # 构建函数定义文本
        definitions_text = ""
        if func_defs:
            definitions_text = "\n\nFunction Definitions:\n"
            for name, defn in func_defs.items():
                definitions_text += f"{name}:\n{defn}\n\n"
        
        # 构建引理概念文本
        lemmas_text = ""
        if lemma_concepts:
            lemmas_text = "\n\nSuggested Lemmas:\n"
            for i, lemma in enumerate(lemma_concepts, 1):
                lemmas_text += f"{i}. {lemma['name']}: {lemma['description']}\n"
        
        prompt = f"""Generate a formal Isabelle/Isar proof sketch for the following theorem.
Use lemmas to decompose the problem into smaller, more manageable pieces.

Theorem Name: {theorem_name}

Formal Theorem Statement:
{formal_statement}
{definitions_text}
"""

        if iteration > 1 and isabelle_error:
            prompt += f"""

Isabelle verification FAILED. Here is the error feedback (verbatim):
{isabelle_error}
"""

        if iteration > 1 and previous_sketch:
            prompt += f"""

Here is the previous failed theory/sketch. Revise it to fix the error:
{previous_sketch}
"""
        
        if informal_proof:
            prompt += f"""
Informal Proof:
{informal_proof}
"""
        
        if lemmas_text:
            prompt += lemmas_text
        
        prompt += """

CRITICAL: Generate COMPLETE proofs WITHOUT using "sorry"!
CRITICAL: NEVER use "where" in proof statements (have, show, etc.)!
  - "where" is ONLY for definitions, NOT for proofs
  - WRONG: have "(x, y) = f z" where "x = a" and "y = b"
  - CORRECT: obtain x y where "(x, y) = f z" and "x = a" and "y = b" by auto
  - CORRECT: have "(x, y) = f z" by (simp add: some_lemma)
  - Use "obtain" to introduce variables with conditions
  - Use "let ?x = ..." for local definitions

Generate the complete proof sketch including:
1. Helper lemmas with COMPLETE proofs (use actual Isabelle tactics, NO "sorry", NO "where" in proofs)
2. The main theorem proof that uses these lemmas with COMPLETE proof steps (NO "sorry", NO "where" in proofs)

Format:
lemma lemma1_name: "..."
proof -
  (* Provide complete proof here using Isabelle tactics *)
  by auto  (* or by simp, by blast, etc. *)
qed

lemma lemma2_name: "..."
proof -
  (* Provide complete proof here *)
  by simp
qed

theorem {theorem_name}: "..."
proof -
  have h1: ... using lemma1_name by auto
  have h2: ... using lemma2_name by auto
  (* Complete the proof with actual tactics *)
  show ?thesis using h1 h2 by auto
qed

REMEMBER: NO "sorry" ALLOWED! Use actual Isabelle proof tactics.

Now output the Isabelle code ONLY, wrapped in markers:
<ISABELLE>
... Isabelle/Isar code ...
</ISABELLE>
"""
        
        try:
            sketch = self.llm.generate(prompt, system_prompt)
            sketch = self._clean_sketch(sketch)
            logger.info(f"生成草图完成，长度: {len(sketch)}")
            return sketch
        except Exception as e:
            logger.error(f"生成草图失败: {e}")
            raise
    
    def _extract_formal_proof_sketch(self, text: str) -> Optional[str]:
        """从 ## Formal proof（或 ## Formal proof sketch）段提取 ```isabelle``` 内代码（若存在）。"""
        m = re.search(
            r"##\s*Formal\s+proof(?:\s+sketch)?\s*(.*)\Z",
            text,
            re.DOTALL | re.IGNORECASE,
        )
        if not m:
            return None
        section = m.group(1).strip()
        fence = "```"
        fm = re.search(
            fence + r"\s*isabelle\s*(.*?)" + fence,
            section,
            re.DOTALL | re.IGNORECASE,
        )
        if fm:
            inner = fm.group(1).strip()
            return inner if inner else None
        section = re.sub(r"^\s*\{\{", "", section)
        section = re.sub(r"\}\}\s*$", "", section)
        section = section.strip()
        return section if section else None

    def _extract_isabelle_fence(self, text: str) -> Optional[str]:
        """论文 2.2.2/图 2-4：从仅含 ```isabelle``` 代码块的响应中抽取证明体。"""
        for block in re.findall(
            r"```\s*(?:isabelle)?\s*\n?(.*?)```", text or "", re.DOTALL | re.IGNORECASE
        ):
            body = (block or "").strip()
            if re.search(r"\b(proof|qed|theorem|lemma|have|show|obtain|hence)\b", body):
                return body
        return None

    def _clean_sketch(self, sketch: str) -> str:
        """
        清理和规范化草图，并检查是否包含sorry和Lean语法
        
        Args:
            sketch: 原始草图
            
        Returns:
            str: 清理后的草图
        """
        raw = sketch
        extracted = self._extract_formal_proof_sketch(raw)
        if extracted is None:
            # 论文 2.2.2/图 2-4：模型可能只输出 ```isabelle ... ``` 证明体（无 ## Formal proof 段头）
            extracted = self._extract_isabelle_fence(raw)
        if extracted is not None:
            sketch = extracted
        else:
            # 移除markdown代码块标记（内置提示词路径）
            sketch = re.sub(r"```isabelle\s*", "", raw)
            sketch = re.sub(r"```\s*$", "", sketch)
            sketch = re.sub(r"^```\s*", "", sketch, flags=re.MULTILINE)

        # 优先提取 marker 内的 Isabelle 代码
        marker_match = re.search(r"<ISABELLE>\s*(.*?)\s*</ISABELLE>", sketch, re.DOTALL | re.IGNORECASE)
        if marker_match:
            sketch = marker_match.group(1)
        else:
            # 回退：剥离常见“解释性文本”，只保留 Isabelle 片段
            lines = sketch.splitlines()
            kept = []
            started = False
            stop_patterns = (
                r"^\s*Here is\b",
                r"^\s*\*\*",
                r"^\s*Explanation\b",
                r"^\s*Key aspects\b",
                r"^\s*All proofs\b",
                r"^\s*The structure\b",
            )
            start_patterns = (
                r"^\s*(theory|imports|begin|end)\b",
                r"^\s*proof\b",
                r"^\s*(lemma|theorem|corollary)\b",
                r"^\s*(definition|abbreviation|fun|function|datatype|type_synonym)\b",
                r"^\s*\(\*",
            )
            stop_re = re.compile("|".join(stop_patterns))
            start_re = re.compile("|".join(start_patterns))

            for ln in lines:
                if started and stop_re.search(ln):
                    break
                if not started:
                    if start_re.search(ln):
                        started = True
                        kept.append(ln)
                    else:
                        continue
                else:
                    kept.append(ln)
            sketch = "\n".join(kept)
        
        # 移除多余空白行
        sketch = re.sub(r'\n{3,}', '\n\n', sketch)
        
        # 检查并替换Lean语法（:=）为Isabelle语法
        # Lean: have h: ... := lemma_name
        # Isabelle: have h: ... using lemma_name by auto
        if re.search(r':=\s*[a-zA-Z_][a-zA-Z0-9_]*', sketch):
            logger.warning("检测到Lean语法（:=），正在替换为Isabelle语法")
            # 替换 have h: ... := lemma_name 为 have h: ... using lemma_name by auto
            sketch = re.sub(
                r'(have\s+\w+:\s*[^:]+):=\s*([a-zA-Z_][a-zA-Z0-9_]*)',
                r'\1using \2 by auto',
                sketch
            )
        
        # 检查并修复错误的"where"使用（在证明语句中）
        # where只能在定义中使用，不能在证明中使用（have, show等）
        # 错误: have "... = ..." where "x = ..." and "y = ..."
        # 正确: obtain x y where "... = ..." and "x = ..." and "y = ..." by ...
        # 或者: have "... = ..." by (simp add: some_lemma)
        
        # 检测have/show/fix等证明语句中的where使用（支持多行）
        proof_keywords = r'\b(have|show|fix|assume)\s+'
        if re.search(f'{proof_keywords}[^:]+:\\s*[^w]+where\\b', sketch, re.MULTILINE):
            logger.warning("检测到在证明语句中使用了'where'，正在修复")
            
            # 匹配模式：have/show/fix/assume ... : ... where ... (可能跨多行)
            # 使用DOTALL模式匹配跨行的where子句
            def remove_where_clause(match):
                # 获取匹配的完整内容
                full_text = match.group(0)
                # 找到where的位置
                where_pos = full_text.find('where')
                if where_pos > 0:
                    # 保留where之前的部分
                    before_where = full_text[:where_pos].rstrip()
                    # 如果before_where以引号结尾，需要处理
                    before_where = re.sub(r'["\']\s*$', '"', before_where)
                    # 添加by auto（如果还没有by语句）
                    if 'by' not in before_where:
                        return before_where + ' by auto'
                    return before_where
                return full_text
            
            # 更简单可靠的替换：直接移除where及其后的内容（支持多行）
            # 匹配到下一个语句开始或行尾
            # 对于have/show，移除where并添加by auto
            sketch = re.sub(
                r'(\bhave\s+[^:]+:\s*[^w]+)\s+where\s+[^\n]*(?:\n\s+[^\n]+)*(?=\n\s*(?:have|show|then|also|finally|qed|next|case|proof|end))?',
                r'\1 by auto',
                sketch,
                flags=re.MULTILINE
            )
            sketch = re.sub(
                r'(\bshow\s+[^:]+:\s*[^w]+)\s+where\s+[^\n]*(?:\n\s+[^\n]+)*(?=\n\s*(?:have|show|then|also|finally|qed|next|case|proof|end))?',
                r'\1 by auto',
                sketch,
                flags=re.MULTILINE
            )
            # 对于fix/assume，只移除where部分
            sketch = re.sub(
                r'(\bfix\s+[^:]+:\s*[^w]+)\s+where\s+[^\n]*(?:\n\s+[^\n]+)*',
                r'\1',
                sketch,
                flags=re.MULTILINE
            )
            sketch = re.sub(
                r'(\bassume\s+[^:]+:\s*[^w]+)\s+where\s+[^\n]*(?:\n\s+[^\n]+)*',
                r'\1',
                sketch,
                flags=re.MULTILINE
            )
        
        # 检查是否包含 sorry（sledgehammer 草图风格下不强行替换）
        if (
            re.search(r"\bsorry\b", sketch, re.IGNORECASE)
            and "sledgehammer" not in sketch.lower()
        ):
            logger.warning("生成的草图中包含'sorry'，尝试替换为基本证明策略")
            # 尝试替换sorry为基本证明策略
            # 在proof块中的sorry替换为by auto
            sketch = re.sub(
                r'(\bproof\s+-.*?)\bsorry\b',
                r'\1by auto',
                sketch,
                flags=re.DOTALL | re.IGNORECASE
            )
            # 单独一行的sorry替换为by auto
            sketch = re.sub(
                r'^\s*sorry\s*$',
                '  by auto',
                sketch,
                flags=re.MULTILINE | re.IGNORECASE
            )
            
            # 再次检查
            if re.search(r'\bsorry\b', sketch, re.IGNORECASE):
                logger.error("警告：草图中仍包含'sorry'，请检查生成的证明")
        
        # 确保以换行符结尾
        if sketch and not sketch.endswith('\n'):
            sketch += '\n'
        
        return sketch.strip()
    
    def extract_lemmas_from_sketch(self, sketch: str) -> List[str]:
        """
        从草图中提取引理陈述
        
        Args:
            sketch: Isabelle草图
            
        Returns:
            List[str]: 引理陈述列表
        """
        lemmas = self.parser.extract_lemmas(sketch)
        return [lemma.statement for lemma in lemmas if lemma.statement_type in ['lemma', 'theorem']]

