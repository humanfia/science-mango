# HumanizePhysics

研究进展：[M6 完整证明、算法验证与验收结果](research/quantum_m6/README.md) · [M1–M8 路线图](research/quantum_m6/ROADMAP.md)。

新增：[量子码研究 harness](pipelines/quantum_humanize/README.md) — 导入当前 M5 推导所用的 Humanize 流程、完整控制测试及运行说明。它使用独立的 Python 3.12 环境和外部研究仓库；并已增加 [LeanExplore 双库检索与 Lean 编译修复、验收入口](pipelines/quantum_formalize/README.md)。

**Autonomous Lean 4 Formalization System** — 自动将数学定理与物理问题转化为经过验证的 Lean 4 形式化证明。

HumanizePhysics 利用 AI（Claude / OpenAI Codex）驱动的多阶段流水线，自动完成从自然语言问题到 Lean 4 机器可验证证明的全过程。

---

## 目录

- [快速开始](#快速开始)
- [启动脚本](#启动脚本-scriptsrunsh)
- [环境变量](#环境变量)
- [项目结构](#项目结构)
- [技术栈](#技术栈)
- [常用命令](#常用命令)
- [文档](#文档)

---

## 快速开始

```bash
# 1. 安装系统依赖（Lean 4 / elan / Node.js 等）
humanizephysics setup

# 2. 初始化一个项目目录
humanizephysics init <project-dir>

# 3. 启动证明循环
scripts/run.sh <project-dir>
```

---

## 启动脚本 (`scripts/run.sh`)

`scripts/run.sh` 是 HumanizePhysics 的 **一键启动入口**，适用于无人值守的批量证明场景（CI / 远程服务器 / 定时任务）。

### 用法

```bash
# 使用默认项目路径启动
./scripts/run.sh

# 指定项目目录启动
./scripts/run.sh /path/to/your/project
```

### 脚本做了什么

1. **设置 PATH** — 将 `elan`（Lean 工具链管理器）、`Node.js v22` 和 `npm` 加入 `PATH`，确保运行环境完整。
2. **切换到 HumanizePhysics 根目录** — 进入 `$HUMANIZEPHYSICS_ROOT`（默认 `/home/ma-user/Python_project/HumanizePhysics`）。
3. **执行证明循环** — 调用 `humanizephysics loop`，以 **prover-only** 模式（`--from prover`）运行，跳过前置的形式化/提取阶段，直接进入证明求解。
4. **无 Dashboard** — 使用 `--no-dashboard` 以纯命令行模式运行，适合 headless 服务器。

### 可配置的环境变量

| 变量 | 默认值 | 说明 |
|---|---|---|
| `HUMANIZEPHYSICS_ROOT` | `/home/ma-user/Python_project/HumanizePhysics` | HumanizePhysics 安装根目录 |
| `HUMANIZEPHYSICS_MAX_ITERATIONS` | `1` | 每个目标的最大证明迭代次数 |
| `HUMANIZEPHYSICS_MAX_PARALLEL` | `4` | 同时并行证明的目标数量 |
| `HUMANIZEPHYSICS_MAX_OBJECTIVES` | `10` | 单次运行处理的最大目标数量 |

**示例：高并发运行**

```bash
HUMANIZEPHYSICS_MAX_PARALLEL=8 HUMANIZEPHYSICS_MAX_ITERATIONS=3 HUMANIZEPHYSICS_MAX_OBJECTIVES=50 \
  ./scripts/run.sh /path/to/project
```

---

## 项目结构

```
HumanizePhysics/
├── scripts/
│   └── run.sh                  # ⭐ 启动脚本（入口）
├── src/humanizephysics/
│   ├── cli.py                  # CLI 入口 (typer)
│   ├── agent.py                # AI Agent 封装 (Claude CLI)
│   ├── prompts.py              # Prompt 模板
│   ├── dispatch.py             # Harness 路由 (Claude / Codex)
│   ├── log.py                  # 日志系统
│   ├── types.py                # 类型定义 (Pydantic)
│   └── commands/
│       ├── loop/               # 主证明循环编排
│       ├── prove.py            # 单目标证明
│       ├── physics_formalize.py # 物理问题自动形式化
│       ├── setup/              # 依赖安装
│       ├── init/               # 项目初始化
│       └── ...
├── docs/                       # 文档
├── tests/                      # 测试 (pytest)
├── pyproject.toml              # 包元数据 & 依赖
└── .venv/                      # Python 虚拟环境
```

---

## 技术栈

| 层 | 技术 |
|---|---|
| 语言 | Python 3.10+ |
| CLI 框架 | Typer + Click |
| AI 后端 | Claude Code CLI, OpenAI SDK |
| 定理证明器 | Lean 4 (via elan) |
| 依赖图分析 | leandag, lean-explore |
| Dashboard | Node.js 22 + Express + Vue.js |
| 数据校验 | Pydantic |
| 测试 | pytest |

---

## 常用命令

```bash
humanizephysics setup              # 安装系统依赖 (elan, Node.js 等)
humanizephysics init <dir>         # 初始化项目目录
humanizephysics loop <dir>         # 启动证明循环
humanizephysics prove <file>       # 对单个文件运行证明
humanizephysics doctor             # 检查环境是否就绪
humanizephysics dashboard          # 启动 Web Dashboard
humanizephysics --help             # 查看所有命令
```

---

## 文档

- [CONFIGURATION.md](docs/CONFIGURATION.md) — 项目配置详解
- [MULTILANE.md](docs/MULTILANE.md) — 多通道并行证明
- [MIGRATION.md](docs/MIGRATION.md) — 版本迁移指南
- [CHANGELOG.md](docs/CHANGELOG.md) — 变更日志

---

## License

详见项目 License 文件。
