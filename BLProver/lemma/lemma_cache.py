"""
引理缓存系统
支持内存缓存和持久化存储
"""

import logging
from typing import List, Optional, Tuple, Dict
from .lemma import Lemma
from .lemma_matcher import LemmaMatcher, MatchType
from .lemma_chroma_storage import LemmaChromaStorage
from ..config import LemmaCacheConfig

logger = logging.getLogger(__name__)


def chroma_embedding_function_for_config(config: LemmaCacheConfig):
    """
    与已验证引理库一致的 embedding，供未证明引理 collection 复用。
    """
    if config.chroma_embedding == "openai":
        from chromadb.utils import embedding_functions
        import os

        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ValueError(
                "LemmaCacheConfig.chroma_embedding='openai' 但未设置 OPENAI_API_KEY"
            )
        return embedding_functions.OpenAIEmbeddingFunction(
            api_key=api_key,
            api_base=os.getenv("OPENAI_BASE_URL"),
            model_name=os.getenv("OPENAI_EMBEDDING_MODEL", "text-embedding-3-small"),
        )
    return None


class LemmaCache:
    """引理缓存系统"""
    
    def __init__(self, config: Optional[LemmaCacheConfig] = None):
        """
        初始化引理缓存
        
        Args:
            config: 缓存配置
        """
        self.config = config or LemmaCacheConfig()
        self.matcher = LemmaMatcher(self.config.similarity_threshold)

        self.chroma_storage: Optional[LemmaChromaStorage] = None
        self._cache: Dict[str, Lemma] = {}

        if not self.config.chroma_enabled:
            logger.info(
                "ChromaDB 已证引理库已禁用（chroma_enabled=False）；"
                "不读写 %s（collection=%s）",
                self.config.chroma_path,
                self.config.chroma_collection,
            )
            return

        embedding_fn = chroma_embedding_function_for_config(self.config)

        self.chroma_storage = LemmaChromaStorage(
            chroma_path=self.config.chroma_path,
            collection_name=self.config.chroma_collection,
            embedding_function=embedding_fn,
        )

        # 从持久化存储加载
        self._load_from_storage()
    
    def _load_from_storage(self):
        """从 ChromaDB 持久化目录加载引理到内存字典 _cache。"""
        if not self.chroma_storage:
            return
        lemmas = self.chroma_storage.get_all()

        for lemma in lemmas:
            cache_key = self._get_cache_key(lemma.statement)
            self._cache[cache_key] = lemma

        logger.info(
            "从 ChromaDB 加载了 %d 个引理到内存（path=%s, collection=%s）",
            len(lemmas),
            self.config.chroma_path,
            self.config.chroma_collection,
        )
    
    def _get_cache_key(self, statement: str) -> str:
        """生成缓存键"""
        # 使用标准化后的语句作为key
        normalized = self.matcher.parser.normalize_statement(statement)
        return hash(normalized)
    
    def add(self, lemma: Lemma) -> bool:
        """
        添加引理到缓存
        
        Args:
            lemma: 要添加的引理
            
        Returns:
            bool: 是否成功
        """
        cache_key = self._get_cache_key(lemma.statement)
        
        # 检查是否已存在
        if cache_key in self._cache:
            logger.debug(f"引理已存在于缓存: {lemma.statement[:50]}...")
            return False
        
        self._cache[cache_key] = lemma

        if self.chroma_storage:
            self.chroma_storage.upsert_lemma(lemma)
        
        logger.info(f"添加引理到缓存: {lemma.statement[:50]}...")
        return True
    
    def get(self, statement: str, match_type: MatchType = MatchType.EXACT) -> Optional[Lemma]:
        """
        获取引理（精确匹配）
        
        Args:
            statement: 引理陈述
            match_type: 匹配类型
            
        Returns:
            Optional[Lemma]: 找到的引理，不存在返回None
        """
        cache_key = self._get_cache_key(statement)
        
        # 先尝试精确匹配
        if cache_key in self._cache:
            lemma = self._cache[cache_key]
            lemma.mark_used()
            return lemma
        
        # 如果精确匹配失败，尝试其他匹配方式
        if match_type != MatchType.EXACT:
            return self.find(statement, match_type)
        
        return None
    
    def find(
        self, 
        statement: str, 
        match_type: MatchType = MatchType.SIMILARITY
    ) -> Optional[Tuple[Lemma, MatchType, float]]:
        """
        查找匹配的引理
        
        Args:
            statement: 要查找的引理陈述
            match_type: 匹配类型
            
        Returns:
            Optional[Tuple[Lemma, MatchType, float]]: (引理, 匹配类型, 相似度)
        """
        # 如果启用 Chroma 后端，把相似度检索交给向量检索；EXACT/NORMALIZED 仍可走本地 matcher
        if self.chroma_storage and match_type == MatchType.SIMILARITY:
            hits = self.chroma_storage.query(statement, k=1)
            if hits:
                lemma, dist = hits[0]
                lemma.mark_used()
                # 将距离转成“分数”用于展示：score = -distance（仅用于排序/展示）
                return lemma, MatchType.SIMILARITY, -float(dist)

        lemmas = list(self._cache.values())
        result = self.matcher.find_best_match(statement, lemmas, [match_type])
        
        if result:
            lemma, match_type, score = result
            lemma.mark_used()
            return lemma, match_type, score
        
        return None
    
    def find_all(
        self,
        statement: str,
        match_types: List[MatchType] = None
    ) -> List[Tuple[Lemma, MatchType, float]]:
        """
        查找所有匹配的引理
        
        Args:
            statement: 要查找的引理陈述
            match_types: 要尝试的匹配类型列表
            
        Returns:
            List[Tuple[Lemma, MatchType, float]]: 匹配结果列表
        """
        if match_types is None:
            match_types = [MatchType.EXACT, MatchType.NORMALIZED, MatchType.SIMILARITY]

        # Chroma 向量检索：只处理 SIMILARITY 部分；其它类型仍用本地 matcher
        if self.chroma_storage and MatchType.SIMILARITY in match_types:
            hits = self.chroma_storage.query(statement, k=10)
            out: List[Tuple[Lemma, MatchType, float]] = []
            for lemma, dist in hits:
                out.append((lemma, MatchType.SIMILARITY, -float(dist)))

            # 如果用户只要相似度，直接返回
            other = [t for t in match_types if t != MatchType.SIMILARITY]
            if not other:
                return out

            # 否则把其它匹配也做了并合并（去重按 statement）
            existing = {l.statement for (l, _, _) in out}
            for lemma in list(self._cache.values()):
                for t in other:
                    match, score = self.matcher.match(statement, lemma, t)
                    if match and lemma.statement not in existing:
                        out.append((lemma, t, score))
                        existing.add(lemma.statement)
                        break
            out.sort(key=lambda x: x[2], reverse=True)
            return out
        
        lemmas = list(self._cache.values())
        results = []
        
        for lemma in lemmas:
            for match_type in match_types:
                match, score = self.matcher.match(statement, lemma, match_type)
                if match:
                    results.append((lemma, match_type, score))
                    break  # 每个引理只添加一次（使用最佳匹配）
        
        # 按相似度排序
        results.sort(key=lambda x: x[2], reverse=True)
        
        return results
    
    def update(self, statement: str, updates: dict) -> bool:
        """
        更新引理
        
        Args:
            statement: 引理陈述
            updates: 要更新的字段字典
            
        Returns:
            bool: 是否成功
        """
        cache_key = self._get_cache_key(statement)
        
        if cache_key not in self._cache:
            logger.warning(f"未找到要更新的引理: {statement[:50]}...")
            return False
        
        lemma = self._cache[cache_key]
        for key, value in updates.items():
            if hasattr(lemma, key):
                setattr(lemma, key, value)

        if self.chroma_storage:
            self.chroma_storage.upsert_lemma(lemma)
        
        logger.info(f"更新引理: {statement[:50]}...")
        return True
    
    def remove(self, statement: str) -> bool:
        """
        移除引理
        
        Args:
            statement: 引理陈述
            
        Returns:
            bool: 是否成功
        """
        cache_key = self._get_cache_key(statement)
        
        if cache_key not in self._cache:
            logger.warning(f"未找到要删除的引理: {statement[:50]}...")
            return False
        
        del self._cache[cache_key]

        if self.chroma_storage:
            self.chroma_storage.delete_lemma(statement)
        
        logger.info(f"删除引理: {statement[:50]}...")
        return True
    
    def get_all(self) -> List[Lemma]:
        """
        获取所有引理
        
        Returns:
            List[Lemma]: 引理列表
        """
        return list(self._cache.values())
    
    def get_verified(self) -> List[Lemma]:
        """
        获取所有已验证的引理
        
        Returns:
            List[Lemma]: 已验证的引理列表
        """
        return [lemma for lemma in self._cache.values() if lemma.status == "verified"]
    
    def size(self) -> int:
        """获取缓存大小"""
        return len(self._cache)
    
    def clear(self):
        """清空缓存"""
        self._cache.clear()
        logger.info("缓存已清空")
    
    def save(self) -> bool:
        """
        保存缓存到持久化存储
        
        Returns:
            bool: 是否成功
        """
        # Chroma upsert is already durable; keep method for API compatibility.
        return True

