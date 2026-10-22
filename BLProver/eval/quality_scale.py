"""
质量分量纲标定。

论文 3.1.4 的综合质量评分 Q(i) = D(i) * U(i) / S(i) 在本题域的量级约 0.02~0.12
（D、U 多为 1，S 约 13~34），阅读与手算都不方便。这里把整条质量量纲
（Q 值、差异化衰减量 Delta_i、淘汰阈值 Qmin）统一放大 Q_SCALE 倍：

    Q(i)    = Q_SCALE * U(i) * D(i) / S(i)
    Delta_i = Delta0 * 来源系数 * 线性系数，Delta0 = 0.01 * Q_SCALE
    Qmin    = 0.01 * Q_SCALE

放大只改变量纲，不改变相对大小、筛选顺序与淘汰结果。
论文 3.2.2 的未放大量纲（Delta0 = Qmin = 0.03）见 config.PaperParamConfig 注释。
"""

from __future__ import annotations

Q_SCALE = 100.0
"""质量分放大倍数：Q(i)、Delta_i、Qmin 统一乘以该系数。"""

CALIBRATED_DECAY_BASE = 0.01
"""本项目按实测 Q(i) 量级标定的 Delta0（论文原值 0.03 的 1/3，未放大量纲）。"""

CALIBRATED_Q_MIN = 0.01
"""本项目按实测 Q(i) 量级标定的 Qmin（论文原值 0.03，未放大量纲）。"""

LEGACY_Q_SCALE = 1.0
"""放大前的历史量纲系数：旧 run 落盘数据未写量纲标记载时按该量纲换算。"""


def scale_q(value: float, from_scale: float = LEGACY_Q_SCALE) -> float:
    """把某个历史量纲下的 Q 值换算为当前量纲。"""
    if from_scale <= 0:
        from_scale = LEGACY_Q_SCALE
    return round(float(value) * Q_SCALE / from_scale, 6)
