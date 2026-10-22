"""
引理匹配器
支持精确匹配、标准化匹配、相似度匹配
"""

from enum import Enum
from typing import Optional, Tuple, List
from .lemma import Lemma
from ..utils.isabelle_parser import IsabelleParser
from ..utils.similarity import jaccard_similarity, tokenize_isabelle


class MatchType(Enum):
    """匹配类型"""
    EXACT = "exact"              # 精确匹配
    NORMALIZED = "normalized"    # 标准化匹配
    SIMILARITY = "similarity"    # 相似度匹配


class LemmaMatcher:
    """引理匹配器"""
    
    def __init__(self, similarity_threshold: float = 0.92):
        """
        初始化匹配器

        Args:
            similarity_threshold: 相似度匹配阈值，默认 0.92（论文 2.4.2）
        """
        self.similarity_threshold = similarity_threshold
        self.parser = IsabelleParser()
    
    def match(
        self, 
        statement: str, 
        lemma: Lemma,
        match_type: MatchType = MatchType.EXACT
    ) -> Tuple[bool, float]:
        """
        匹配引理
        
        Args:
            statement: 要匹配的引理陈述
            lemma: 候选引理
            match_type: 匹配类型
            
        Returns:
            Tuple[bool, float]: (是否匹配, 相似度分数)
        """
        if match_type == MatchType.EXACT:
            return self._exact_match(statement, lemma.statement)
        elif match_type == MatchType.NORMALIZED:
            return self._normalized_match(statement, lemma.statement)
        elif match_type == MatchType.SIMILARITY:
            return self._similarity_match(statement, lemma.statement)
        else:
            return False, 0.0
    
    def _exact_match(self, stmt1: str, stmt2: str) -> Tuple[bool, float]:
        """
        精确匹配
        
        Args:
            stmt1: 第一个陈述
            stmt2: 第二个陈述
            
        Returns:
            Tuple[bool, float]: (是否匹配, 相似度1.0或0.0)
        """
        normalized1 = stmt1.strip()
        normalized2 = stmt2.strip()
        match = normalized1 == normalized2
        return match, 1.0 if match else 0.0
    
    def _normalized_match(self, stmt1: str, stmt2: str) -> Tuple[bool, float]:
        """
        标准化匹配（忽略变量名差异）
        
        Args:
            stmt1: 第一个陈述
            stmt2: 第二个陈述
            
        Returns:
            Tuple[bool, float]: (是否匹配, 相似度)
        """
        # 标准化语句
        normalized1 = self.parser.normalize_statement(stmt1)
        normalized2 = self.parser.normalize_statement(stmt2)
        
        # 尝试标准化变量名（简单方法：提取结构）
        # 更复杂的方法需要完整的Isabelle解析器
        
        # 先尝试精确匹配标准化后的结果
        if normalized1 == normalized2:
            return True, 1.0
        
        # 使用token集合比较
        tokens1 = tokenize_isabelle(normalized1)
        tokens2 = tokenize_isabelle(normalized2)
        
        similarity = jaccard_similarity(tokens1, tokens2)
        match = similarity >= 0.95  # 标准化匹配需要更高的阈值
        
        return match, similarity
    
    def _similarity_match(self, stmt1: str, stmt2: str) -> Tuple[bool, float]:
        """
        相似度匹配（基于Jaccard相似度）
        
        Args:
            stmt1: 第一个陈述
            stmt2: 第二个陈述
            
        Returns:
            Tuple[bool, float]: (是否匹配, 相似度)
        """
        tokens1 = tokenize_isabelle(stmt1)
        tokens2 = tokenize_isabelle(stmt2)
        
        similarity = jaccard_similarity(tokens1, tokens2)
        match = similarity >= self.similarity_threshold
        
        return match, similarity
    
    def find_best_match(
        self,
        statement: str,
        lemmas: List[Lemma],
        match_types: List[MatchType] = None
    ) -> Optional[Tuple[Lemma, MatchType, float]]:
        """
        查找最佳匹配的引理
        
        Args:
            statement: 要匹配的引理陈述
            lemmas: 候选引理列表
            match_types: 要尝试的匹配类型列表，默认按优先级顺序
            
        Returns:
            Optional[Tuple[Lemma, MatchType, float]]: (最佳匹配引理, 匹配类型, 相似度)
        """
        if match_types is None:
            match_types = [MatchType.EXACT, MatchType.NORMALIZED, MatchType.SIMILARITY]
        
        best_match = None
        best_score = 0.0
        best_type = None
        
        for lemma in lemmas:
            for match_type in match_types:
                match, score = self.match(statement, lemma, match_type)
                
                if match and score > best_score:
                    best_match = lemma
                    best_score = score
                    best_type = match_type
        
        if best_match:
            return best_match, best_type, best_score
        
        return None

