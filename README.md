# BLProver

基于大语言模型与 Isabelle/HOL 的线性数据结构定理证明流水线：从定理陈述生成证明草图与辅助引理，在 Isabelle 中验证，对引理库做质量评估与筛选，最终输出可复用的领域引理库和单定理交付包。

## 环境要求

- Python 3.9+
- Isabelle2025（需可用的 Isabelle server）
- 可访问的 OpenAI 兼容 LLM 接口

## 安装

```bash
pip install -r requirements.txt
```

## 配置

复制 `.env.example` 为 `.env`，填写：

```ini
OPENAI_API_KEY=你的密钥
OPENAI_BASE_URL=https://api.deepseek.com
# 可选
BLPROVER_MODEL=deepseek-v4-pro
```

Isabelle 默认路径为 `D:/software/Isabelle2025/Isabelle2025`。其他机器用 `--isabelle-home` 与 `--isabelle-path` 覆盖。

## 启动指令

证明单条定理：

```bash
python -m BLProver.main --single data/list/before_in_setD2.json --delivery-dir results_fullproof
```

按目录批量证明（`--count` 限制条数，省略则跑完整个目录）：

```bash
python -m BLProver.main --data-dir data/list --count 5 --delivery-dir results_fullproof
```

只对已有产物重算引理质量评估与筛选：

```bash
python -m BLProver.main --quality-eval-only --delivery-dir results_fullproof
```

只验证一个已有的 `.thy` 文件：

```bash
python -m BLProver.main --verify-thy-file path/to/Theorem.thy
```

常用参数：

| 参数 | 说明 |
| --- | --- |
| `--single`, `-s` | 指定单个定理 JSON |
| `--data-dir`, `-d` | 定理数据目录，默认 `./data` |
| `--output-dir`, `-o` | 运行目录，默认 `./output` |
| `--count`, `-n` | 批量运行时限制定理条数 |
| `--delivery-dir` | 最终交付包根目录 |
| `--model` | LLM 模型名 |
| `--isabelle-home` | Isabelle 安装目录 |
| `--isabelle-path` | Isabelle bash 可执行文件 |
| `--isabelle-verify-wall-timeout` | 单次验证墙钟超时（秒） |
| `--sledgehammer-rounds` | Sledgehammer 回填轮数 |
| `--repair-rounds` | 按报错行修复的轮数 |
| `--no-prove-used-lemmas` | 不证明主定理引用的引理 |
| `--skip-sledgehammer` | 跳过 Sledgehammer 与 Isabelle 验证 |
| `--no-delivery` | 不生成交付包 |
| `--quality-eval-only` | 只跑质量评估与筛选 |

## 运行流程

1. 读取定理 JSON：定理名、形式化陈述、函数定义、依赖包。
2. 四阶段提示词流程：全局引理生成 -> 非形式证明 -> 中间引理提取 -> 形式证明草图。
3. 生成工作理论文件 `<定理>_sketch.thy` 与未证明引理文件 `<定理>_unproven_lemmas.thy`。
4. 在 Isabelle 中验证草图；失败行替换为 Sledgehammer，仍失败则把报错交给 LLM 修复。
5. 逐条证明主定理引用的引理：LLM 证明 -> Isabelle 验证 -> 报错修复；未证成的保留 `sorry`。
6. 生成并验证最终定理；失败则按外层重试重新走草图与引理流程，复用已证引理库。
7. 对引理库做质量评估、来源与线性标签加权衰减、阈值淘汰。
8. 合并领域引理库，导出最终理论与交付包。

## 输出结构

运行中间产物与日志写入 `output/`。最终结果写入 `--delivery-dir`：

```text
results_fullproof/
  <domain>/
    defs.thy                     领域定义（累积）
    proven_lemmas.thy            已证引理（含后来被淘汰的）
    all_constructed_lemmas.thy   全部生成引理（含未证明，以 sorry 留档）
    excellent_lemmas.thy         质量筛选后留存的引理
    lemmas1.thy                  全局引理生成策略
    lemmas2.thy                  中间引理提取策略
    lemmas3.thy                  修复引理构造策略
    <theorem>/
      index.json                 机器可读清单
      theory/                    定理与定义
      lemmas/                    按来源与线性标签归档的引理
      metrics/                   指标
```

## 数据集

`data/` 下按领域存放 JSON 文件，每个文件对应一条定理，字段包括 `theorem name`、`formal theorem statement`、`formal function definitions` 与依赖包。
