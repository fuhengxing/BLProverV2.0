"""
BLProver: 基于引理的 Isabelle 定理证明系统
实现思路参考 BLProver 1.5 方案
"""

__version__ = "1.0.0"

# 启动时自动加载仓库根目录的 .env（本地默认配置，只需配置一次）
from .env_loader import load_env_file

load_env_file()

from .main import BLProver
from .config import BLProverConfig, LLMConfig, LemmaCacheConfig

__all__ = [
    "BLProver",
    "BLProverConfig",
    "LLMConfig",
    "LemmaCacheConfig",
]
