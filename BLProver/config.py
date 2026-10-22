"""
配置管理模块
"""

import os
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Literal
from pathlib import Path


@dataclass
class LLMConfig:
    """LLM配置"""
    model_name: str = "deepseek-v4-pro"
    api_key: Optional[str] = None
    base_url: Optional[str] = None
    temperature: float = 0.7
    max_tokens: int = 65536
    thinking_mode: bool = False
    reasoning_effort: str = "high"


@dataclass
class LemmaQualityEvalConfig:
    """引理质量评估配置（多维度）。"""
    enabled: bool = True
    """总开关：关闭后跳过所有引理质量评估。"""
    syntax_enabled: bool = True
    """维度 1：语法复杂度（Isabelle prop_nodes）。"""
    proof_difficulty_enabled: bool = False
    """维度 2a：证明推导难度（LLM + proof_difficulty_prompt.txt）—— 已禁用，改用维度 2b。"""
    proof_difficulty_v2_enabled: bool = True
    """维度 2b：证明推导难度评分 = used_lemma_count（proof_difficulty_score_v2/）。"""
    syntax_timeout: int = 60
    """语法复杂度：Isabelle 批量分析基础超时（秒）。"""
    proof_difficulty_prompt_path: Optional[str] = None
    """证明难度 prompt；默认 eval/proof_difficulty_score/proof_difficulty_prompt.txt"""


@dataclass
class LemmaCacheConfig:
    """引理缓存配置（ChromaDB 可选；关闭时不读写磁盘，便于保留旧数据供日后启用）。"""
    chroma_enabled: bool = False
    """为 False 时不连接 ChromaDB；./chroma_lemma_db 内已有数据不会被删除或修改。"""
    similarity_threshold: float = 0.92
    """论文 2.4.2 判重阈值：候选引理与库内全部引理的余弦相似度均 < 0.92 才可入库。"""
    chroma_path: str = "./chroma_lemma_db"
    chroma_collection: str = "proven_lemma_chromadb"
    """已验证引理的 Chroma collection。"""
    unproven_collection: str = "unproven_lemma_chromadb"
    """构造阶段产生的未证明引理（独立 collection）。"""
    chroma_embedding: Literal["default", "openai"] = "default"


@dataclass
class PaperParamConfig:
    """论文《基于引理扩充和质量筛选的线性数据结构算法证明》第 3、4 章口径参数。

    质量评分 Q(i) = Q_SCALE * D(i) * U(i) / S(i)（3.1，量纲放大见 eval/quality_scale.py）；
    质量筛选衰减与淘汰（3.2）；外层/内层循环次数与 Sledgehammer 超时（4.1.4）。
    系数表以论文为准；decay_base / q_min 先按实测 Q(i) 量级（Q≈U*D/S，本题域典型
    0.02~0.12）等比缩放 1/3 标定为 0.01，再随 Q_SCALE=100 整体放大到 1.0，
    以复现论文 4.3 的生命周期目标：低质量引理存活 3~5 批、高质量引理存活 8~12 批。
    """

    decay_base: float = 1.0
    """Δ0：基础衰减量；Δ_i = Δ0 * 来源系数 * 线性系数。
    标定值 0.01（论文原值 0.03，按实测 Q(i) 量级缩放 1/3）再放大 Q_SCALE=100 倍，
    与放大后的 Q(i) 同量纲。"""
    q_min: float = 1.0
    """Qmin：淘汰阈值，Q(i) < Qmin 的引理移出引理库。
    标定值 0.01 放大 Q_SCALE=100 倍（论文原值 0.03）。"""
    source_coefficient: Dict[str, float] = field(
        default_factory=lambda: {"global": 0.7, "middle": 1.0, "repair": 1.3}
    )
    """来源系数：全局引理 0.7 / 中间引理 1.0 / 修复引理 1.3（表 3-2）。"""
    linear_coefficient: Dict[str, float] = field(
        default_factory=lambda: {
            "sequence_invariance": 0.7,
            "operation_executability": 0.8,
            "recursion_termination": 0.9,
            "order_preservation": 0.8,
            "nonlinear": 1.2,
        }
    )
    """线性系数：序列不变性 0.7 / 操作可执行性 0.8 / 递归终止性 0.9 / 序关系保持性 0.8；非线性 1.2；多标签取最小。"""
    similarity_threshold: float = 0.92
    """候选引理与库内引理余弦相似度判重阈值：全部 < 该值才可入库（2.4.2）。"""
    outer_regeneration_max: int = 3
    """外层：验证失败后重生成证明草图的最大次数（4.1.4）。"""
    inner_repair_max: int = 3
    """内层：按报错行修复/回填的最大次数（4.1.4）。"""
    sledgehammer_timeout_sec: int = 30
    """Sledgehammer 单次超时（秒，4.1.4）。"""


@dataclass
class BLProverConfig:
    """BLProver主配置"""
    # 路径配置
    output_dir: str = "./output"
    data_dir: str = "./data"
    construct_lemma_prompt_path: Optional[str] = None
    """构造引理提示词文件路径；默认使用包上级的 prompt/construct lemma prompt.txt"""
    sketch_prompt_path: Optional[str] = None
    """草图生成提示词；未配置时使用内置草图提示。"""
    construct_lemmas1_prompt_path: Optional[str] = None
    """四阶段第1步模板：construct_lemmas1_prompt.txt"""
    theorem_to_informal_prompt_path: Optional[str] = None
    """四阶段第2步模板：theoremStatment_to_informalProof_prompt.txt"""
    construct_lemmas2_prompt_path: Optional[str] = None
    """四阶段第3步模板：construct_lemmas2_prompt.txt"""
    informal_to_formal_prompt_path: Optional[str] = None
    """四阶段第4步模板：informalProof_to_formalProof_prompt.txt"""
    sketch_repair_prompt_path: Optional[str] = None
    """验证失败后迭代修复草图：prompt/sketch_repair_after_verify_prompt.txt"""
    lemma_proof_prompt_path: Optional[str] = None
    """被引用引理 LLM 首次证明：lemma_proving/lemma_proof_prompt.txt"""
    lemma_proof_repair_prompt_path: Optional[str] = None
    """引理证明 Isabelle 失败后修复：lemma_proving/lemma_proof_repair_prompt.txt"""
    lemmas_reflection_prompt_path: Optional[str] = None
    """unproven 引理陈述 Isabelle 验证失败后重写：prompt/lemmas_reflection_prompt.txt"""
    repair_lemma_prompt_path: Optional[str] = None
    """修复引理构造提示词：prompt/construct_lemmas3_prompt.txt（论文 2.3.3 图 2-9/2-10）"""
    lemma_revision_prompt_path: Optional[str] = None
    """引理修正机制提示词：prompt/lemmas_reflection.txt（论文 2.3.3 图 2-11/2-12）"""
    
    # 模块配置
    llm: LLMConfig = field(default_factory=LLMConfig)
    lemma_cache: LemmaCacheConfig = field(default_factory=LemmaCacheConfig)
    lemma_quality_eval: LemmaQualityEvalConfig = field(
        default_factory=LemmaQualityEvalConfig
    )
    paper: PaperParamConfig = field(default_factory=PaperParamConfig)
    """论文口径参数（3.2 质量筛选、2.4 判重阈值、4.1.4 循环与超时）。"""
    
    # 运行配置
    max_iterations: int = 5
    max_parallel_workers: int = 4
    log_level: str = "INFO"
    max_sketch_repair_attempts: int = 3
    """Sledgehammer/Isabelle 验证失败后，用错误信息让 LLM 重生成 formal sketch 的最大次数。"""
    sketch_repair_enabled: bool = True
    """是否启用验证失败后的 LLM 草图修复循环。"""
    prove_used_lemmas_after_theorem: bool = True
    theorem_outer_restart_max: int = 3
    """论文 1.4 步骤 5 / 4.3：定理验证失败后外层回溯（重新执行草图构建+引理生成+定理验证）的最大次数；复用在库已证引理。"""
    """主定理 thy_verified 后，对 unproven_lemmas.thy 中全部 sorry 引理做迭代证明。"""
    lemmas_reflection_enabled: bool = True
    """写入 unproven_lemmas.thy 后，验证引理陈述；失败则 LLM 反思重写。"""
    max_lemmas_reflection_attempts: int = 3
    delivery_enabled: bool = True
    """证明成功后是否生成交付包（results/<domain>/<theorem>/）。"""
    delivery_dir: Optional[str] = None
    """交付包根目录；None 表示 <output_dir>/results。"""
    """引理反思：Isabelle 验证 + LLM 修正的最大轮次。"""
    lemma_two_stage_enabled: bool = True
    """引理证明是否走论文 2.5 的两阶段（非形式化证明 -> 形式化草图），复用 2.2.1/2.2.2 模板。"""
    repair_lemma_enabled: bool = True
    """定理草图验证失败后，是否启用修复引理构造策略 + 引理修正机制（论文 2.3.3）。"""
    max_repair_lemma_attempts: int = 3
    """修复引理构造 + 引理修正机制的最大轮次（论文 4.1.4：3 次）。"""
    used_lemma_initial_max_attempts: int = 3
    """每条引理：首次生成（lemma_proof_prompt）+ Isabelle 验证，最多轮次。"""
    used_lemma_repair_max_attempts: int = 3
    """每条引理：单次首次失败后的修复（lemma_proof_repair_prompt）+ 验证，最多轮次。"""
    used_lemma_llm_max_attempts: int = 3
    """已弃用：请用 used_lemma_initial_max_attempts；保留仅为兼容旧 CLI。"""
    
    def __post_init__(self):
        """初始化后处理"""
        # 设置默认LLM API密钥
        if not self.llm.api_key:
            self.llm.api_key = os.getenv("OPENAI_API_KEY")

        # 设置默认LLM Base URL（可选；用于DeepSeek等OpenAI兼容服务）
        if not self.llm.base_url:
            self.llm.base_url = (
                os.getenv("OPENAI_BASE_URL")
                or os.getenv("OPENAI_API_BASE")
            )
        
        # 确保输出目录存在
        Path(self.output_dir).mkdir(parents=True, exist_ok=True)

        pkg_root = Path(__file__).resolve().parent.parent
        if not self.construct_lemma_prompt_path:
            self.construct_lemma_prompt_path = str(
                pkg_root / "prompt" / "construct_lemmas1_prompt.txt"
            )
        if not self.construct_lemmas1_prompt_path:
            self.construct_lemmas1_prompt_path = str(
                pkg_root / "prompt" / "construct_lemmas1_prompt.txt"
            )
        if not self.theorem_to_informal_prompt_path:
            self.theorem_to_informal_prompt_path = str(
                pkg_root / "prompt" / "theoremStatment_to_informalProof_prompt.txt"
            )
        if not self.construct_lemmas2_prompt_path:
            self.construct_lemmas2_prompt_path = str(
                pkg_root / "prompt" / "construct_lemmas2_prompt.txt"
            )
        if not self.informal_to_formal_prompt_path:
            self.informal_to_formal_prompt_path = str(
                pkg_root / "prompt" / "informalProof_to_formalProof_prompt.txt"
            )
        if not self.sketch_repair_prompt_path:
            self.sketch_repair_prompt_path = str(
                pkg_root / "prompt" / "sketch_repair_after_verify_prompt.txt"
            )
        lemma_pkg = Path(__file__).resolve().parent / "lemma_proving"
        if not self.lemma_proof_prompt_path:
            self.lemma_proof_prompt_path = str(
                lemma_pkg / "lemma_proof_prompt.txt"
            )
        if not self.lemma_proof_repair_prompt_path:
            self.lemma_proof_repair_prompt_path = str(
                lemma_pkg / "lemma_proof_repair_prompt.txt"
            )
        if not self.lemmas_reflection_prompt_path:
            self.lemmas_reflection_prompt_path = str(
                pkg_root / "prompt" / "lemmas_reflection_prompt.txt"
            )
        if not self.repair_lemma_prompt_path:
            self.repair_lemma_prompt_path = str(
                pkg_root / "prompt" / "construct_lemmas3_prompt.txt"
            )
        if not self.lemma_revision_prompt_path:
            self.lemma_revision_prompt_path = str(
                pkg_root / "prompt" / "lemmas_reflection.txt"
            )
        if not self.lemma_quality_eval.proof_difficulty_prompt_path:
            self.lemma_quality_eval.proof_difficulty_prompt_path = str(
                Path(__file__).resolve().parent
                / "eval"
                / "proof_difficulty_score"
                / "proof_difficulty_prompt.txt"
            )
