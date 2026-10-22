"""内部提示词路径（不对外暴露）。"""

from pathlib import Path

HIDDEN_FULL_PROOF_PROMPT = (
    Path(__file__).resolve().parent / "_full_proof_prompt.txt"
)
"""隐藏的完整证明提示词：替代旧的四阶段 step4 提示词实际生效。"""
