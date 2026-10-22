"""
LLM接口模块
"""

from .base import LLMInterface
from .openai_llm import OpenAILLM

__all__ = ["LLMInterface", "OpenAILLM"]

