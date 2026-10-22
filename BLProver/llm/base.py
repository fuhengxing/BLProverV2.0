"""
LLM接口基类
定义统一的LLM调用接口
"""

from abc import ABC, abstractmethod
from typing import List, Dict, Optional
import logging

logger = logging.getLogger(__name__)


class LLMInterface(ABC):
    """LLM接口基类"""
    
    @abstractmethod
    def generate(self, prompt: str, system_prompt: str = "") -> str:
        """
        生成文本响应
        
        Args:
            prompt: 用户提示
            system_prompt: 系统提示
            
        Returns:
            str: 生成的文本
        """
        pass
    
    def generate_with_messages(self, messages: List[Dict[str, str]]) -> str:
        """
        使用消息列表生成响应
        
        Args:
            messages: 消息列表，每个消息包含role和content
                role可以是"system"、"user"、"assistant"
            
        Returns:
            str: 生成的文本
        """
        # 默认实现：提取system和user消息
        system_prompt = ""
        user_prompt = ""
        
        for msg in messages:
            role = msg.get("role", "")
            content = msg.get("content", "")
            
            if role == "system":
                system_prompt = content
            elif role == "user":
                # 如果有多个user消息，合并它们
                if user_prompt:
                    user_prompt += "\n\n" + content
                else:
                    user_prompt = content
        
        return self.generate(user_prompt, system_prompt)

