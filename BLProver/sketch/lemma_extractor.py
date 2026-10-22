"""
引理提取器
从自然语言证明中提取引理概念
"""

import re
import logging
from typing import List, Dict, Optional
from ..llm.base import LLMInterface

logger = logging.getLogger(__name__)


class LemmaExtractor:
    """引理提取器"""
    
    def __init__(self, llm: LLMInterface):
        """
        初始化引理提取器
        
        Args:
            llm: LLM接口
        """
        self.llm = llm
    
    def extract_lemmas(
        self,
        theorem_statement: str,
        informal_proof: Optional[str] = None
    ) -> List[Dict[str, str]]:
        """
        从定理和自然语言证明中提取引理概念
        
        Args:
            theorem_statement: 定理陈述
            informal_proof: 自然语言证明（可选）
            
        Returns:
            List[Dict[str, str]]: 引理列表，每个引理包含name和description
        """
        system_prompt = """You are an expert in mathematical theorem proving.
Your task is to identify key lemmas that would help prove the given theorem.
Analyze the theorem statement and informal proof (if provided) to identify intermediate results
that would make the proof easier to construct.

For each lemma, provide:
- A descriptive name
- A clear statement of what needs to be proved

Focus on lemmas that:
1. Break down the problem into smaller, more manageable pieces
2. Capture key mathematical insights from the proof
3. Are self-contained and can be proved independently"""
        
        prompt = f"""Given the following theorem, identify the key lemmas that would help prove it.

Theorem Statement:
{theorem_statement}
"""
        
        if informal_proof:
            prompt += f"""

Informal Proof:
{informal_proof}
"""
        
        prompt += """

Please identify 2-5 key lemmas. For each lemma, provide:
1. A descriptive name (e.g., "zero_poly_to_exist_form_lemma")
2. A clear statement of what needs to be proved

Format your response as:
LEMMA_NAME_1: statement of lemma 1
LEMMA_NAME_2: statement of lemma 2
...
"""
        
        try:
            response = self.llm.generate(prompt, system_prompt)
            lemmas = self._parse_lemmas(response)
            logger.info(f"提取了 {len(lemmas)} 个引理概念")
            return lemmas
        except Exception as e:
            logger.error(f"提取引理失败: {e}")
            return []
    
    def _parse_lemmas(self, response: str) -> List[Dict[str, str]]:
        """
        解析LLM响应，提取引理
        
        Args:
            response: LLM响应文本
            
        Returns:
            List[Dict[str, str]]: 引理列表
        """
        lemmas = []
        
        # 匹配模式：LEMMA_NAME: statement
        pattern = r'([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)(?=\n[A-Z]|\Z)'
        matches = re.findall(pattern, response, re.MULTILINE | re.DOTALL)
        
        for name, description in matches:
            lemmas.append({
                "name": name.strip(),
                "description": description.strip()
            })
        
        # 如果没有匹配到，尝试其他格式
        if not lemmas:
            # 尝试按行分割，每行一个引理
            lines = response.strip().split('\n')
            for i, line in enumerate(lines):
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                
                # 尝试提取引理名和描述
                if ':' in line:
                    parts = line.split(':', 1)
                    if len(parts) == 2:
                        name = parts[0].strip()
                        desc = parts[1].strip()
                        if name and desc:
                            lemmas.append({
                                "name": name,
                                "description": desc
                            })
        
        return lemmas

