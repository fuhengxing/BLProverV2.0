"""
Isabelle语法解析工具
"""

import re
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass


@dataclass
class IsabelleStatement:
    """Isabelle语句结构"""
    statement_type: str  # theorem, lemma, definition, etc.
    name: str
    statement: str
    proof: Optional[str] = None
    variables: List[str] = None
    
    def __post_init__(self):
        if self.variables is None:
            self.variables = []


class IsabelleParser:
    """Isabelle语法解析器"""
    
    # 匹配theorem/lemma/definition等声明
    STATEMENT_PATTERN = re.compile(
        r'(theorem|lemma|definition|corollary|proposition)\s+'
        r'([a-zA-Z_][a-zA-Z0-9_\']*)?\s*'
        r'(?:\[.*?\])?\s*'  # 可选的属性
        r':\s*"(.*?)"',
        re.DOTALL
    )
    
    # 匹配变量绑定
    VARIABLE_PATTERN = re.compile(
        r'\b([a-zA-Z_][a-zA-Z0-9_\']*)\s*::\s*"[^"]*"'
    )
    
    @staticmethod
    def parse_statement(text: str) -> Optional[IsabelleStatement]:
        """
        解析Isabelle语句
        
        Args:
            text: Isabelle代码文本
            
        Returns:
            Optional[IsabelleStatement]: 解析结果，失败返回None
        """
        match = IsabelleParser.STATEMENT_PATTERN.search(text)
        if not match:
            return None
        
        stmt_type = match.group(1)
        name = match.group(2) or ""
        statement = match.group(3).strip()
        
        # 提取变量
        variables = IsabelleParser._extract_variables(text)
        
        # 提取证明（如果有）
        proof = IsabelleParser._extract_proof(text)
        
        return IsabelleStatement(
            statement_type=stmt_type,
            name=name.strip(),
            statement=statement,
            proof=proof,
            variables=variables
        )
    
    @staticmethod
    def _extract_variables(text: str) -> List[str]:
        """提取变量名"""
        variables = []
        matches = IsabelleParser.VARIABLE_PATTERN.findall(text)
        variables.extend(matches)
        return list(set(variables))  # 去重
    
    @staticmethod
    def _extract_proof(text: str) -> Optional[str]:
        """提取证明部分"""
        # 查找proof关键字
        proof_match = re.search(r'\bproof\s+', text, re.IGNORECASE)
        if not proof_match:
            return None
        
        proof_start = proof_match.end()
        
        # 查找qed或sorry
        qed_match = re.search(r'\bqed\b', text[proof_start:], re.IGNORECASE)
        sorry_match = re.search(r'\bsorry\b', text[proof_start:], re.IGNORECASE)
        
        end_pos = len(text)
        if qed_match:
            end_pos = proof_start + qed_match.start()
        elif sorry_match:
            end_pos = proof_start + sorry_match.end()
        
        return text[proof_start:end_pos].strip()
    
    @staticmethod
    def normalize_statement(statement: str) -> str:
        """
        标准化Isabelle语句（用于匹配）
        
        标准化步骤：
        1. 移除多余空白
        2. 标准化变量名（可选，需要更复杂的解析）
        
        Args:
            statement: Isabelle语句
            
        Returns:
            str: 标准化后的语句
        """
        # 移除多余空白
        normalized = re.sub(r'\s+', ' ', statement)
        normalized = normalized.strip()
        
        return normalized
    
    @staticmethod
    def extract_lemmas(text: str) -> List[IsabelleStatement]:
        """
        从文本中提取所有引理
        
        Args:
            text: Isabelle代码文本
            
        Returns:
            List[IsabelleStatement]: 引理列表
        """
        lemmas = []
        
        # 分割为多个语句（简单方法：按theorem/lemma分割）
        parts = re.split(r'(?=\b(theorem|lemma|definition|corollary|proposition)\b)', text)
        
        for part in parts:
            if not part.strip():
                continue
            
            stmt = IsabelleParser.parse_statement(part)
            if stmt:
                lemmas.append(stmt)
        
        return lemmas
    
    @staticmethod
    def is_valid_isabelle_syntax(text: str) -> bool:
        """
        简单检查Isabelle语法是否有效
        
        注意：这只是基本检查，完整验证需要Isabelle编译器
        
        Args:
            text: Isabelle代码文本
            
        Returns:
            bool: 是否看起来像有效的Isabelle语法
        """
        # 检查基本结构
        if not re.search(r'\b(theorem|lemma|definition)\b', text, re.IGNORECASE):
            return False
        
        # 检查引号匹配
        quote_count = text.count('"')
        if quote_count % 2 != 0:
            return False
        
        return True

