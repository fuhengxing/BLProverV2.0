"""
相似度计算工具
"""

import re
from typing import Set, List


def tokenize_isabelle(statement: str) -> Set[str]:
    """
    将Isabelle语句转换为token集合
    
    Args:
        statement: Isabelle语句
        
    Returns:
        Set[str]: token集合
    """
    # 移除注释
    statement = re.sub(r'\(\*.*?\*\)', '', statement, flags=re.DOTALL)
    
    # 移除字符串字面量（保留引号内的内容作为一个token）
    statement = re.sub(r'"[^"]*"', 'STRING', statement)
    
    # 分割为token：标识符、关键字、操作符、标点符号
    # 匹配标识符、关键字、操作符
    tokens = re.findall(r'\b\w+\b|[^\w\s]', statement)
    
    # 过滤空白和空字符串
    tokens = [t.strip() for t in tokens if t.strip()]
    
    # 转换为小写并去重
    return set(t.lower() for t in tokens if t)


def jaccard_similarity(set1: Set[str], set2: Set[str]) -> float:
    """
    计算两个集合的Jaccard相似度
    
    Jaccard相似度 = |A ∩ B| / |A ∪ B|
    
    Args:
        set1: 第一个集合
        set2: 第二个集合
        
    Returns:
        float: Jaccard相似度，范围[0, 1]
    """
    if not set1 and not set2:
        return 1.0
    
    if not set1 or not set2:
        return 0.0
    
    intersection = len(set1 & set2)
    union = len(set1 | set2)
    
    if union == 0:
        return 0.0
    
    return intersection / union


def normalized_edit_distance(s1: str, s2: str) -> float:
    """
    计算归一化编辑距离（Levenshtein距离）
    
    Args:
        s1: 第一个字符串
        s2: 第二个字符串
        
    Returns:
        float: 归一化编辑距离，范围[0, 1]，0表示完全相同
    """
    if not s1 and not s2:
        return 0.0
    
    if not s1:
        return 1.0
    
    if not s2:
        return 1.0
    
    # 计算编辑距离
    m, n = len(s1), len(s2)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    
    for i in range(m + 1):
        dp[i][0] = i
    for j in range(n + 1):
        dp[0][j] = j
    
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if s1[i-1] == s2[j-1]:
                dp[i][j] = dp[i-1][j-1]
            else:
                dp[i][j] = min(
                    dp[i-1][j] + 1,      # 删除
                    dp[i][j-1] + 1,      # 插入
                    dp[i-1][j-1] + 1     # 替换
                )
    
    edit_dist = dp[m][n]
    max_len = max(m, n)
    
    return edit_dist / max_len if max_len > 0 else 0.0

