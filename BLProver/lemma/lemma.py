"""
引理数据类
"""

from dataclasses import dataclass, field, asdict
from typing import Dict, Optional, Any
from datetime import datetime


@dataclass
class Lemma:
    """引理数据结构"""
    statement: str           # 引理陈述
    proof: str              # 证明内容
    status: str = "unverified"  # verified/unverified/failed
    usage_count: int = 0    # 使用次数
    score: float = 0.0      # 评分
    metadata: Dict[str, Any] = field(default_factory=dict)  # 其他元数据
    created_at: str = field(default_factory=lambda: datetime.now().isoformat())
    updated_at: str = field(default_factory=lambda: datetime.now().isoformat())
    
    def to_dict(self) -> Dict:
        """转换为字典"""
        return asdict(self)
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'Lemma':
        """从字典创建"""
        return cls(**data)
    
    def mark_used(self):
        """标记为已使用"""
        self.usage_count += 1
        self.updated_at = datetime.now().isoformat()
    
    def mark_verified(self):
        """标记为已验证"""
        self.status = "verified"
        self.updated_at = datetime.now().isoformat()
    
    def mark_failed(self):
        """标记为失败"""
        self.status = "failed"
        self.updated_at = datetime.now().isoformat()

