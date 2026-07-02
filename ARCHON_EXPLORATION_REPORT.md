# HumanizePhysics Project - Comprehensive Exploration Report

## Executive Summary

**HumanizePhysics** is an autonomous Lean 4 formalization system written in Python that uses AI (Claude and OpenAI Codex) to automatically formalize mathematical theorems and physics problems into the Lean 4 proof assistant. It's a sophisticated orchestration framework for managing multi-phase agent-driven theorem proving.

---

## 1. Overall Project Structure

### Directory Layout
```
HumanizePhysics/
├── src/humanizephysics/                    # Main Python package (54MB)
│   ├── cli.py                     # CLI entrypoint (136 lines)
│   ├── agent.py                   # Claude Code wrapper (1,950 lines) ★ Core
│   ├── prompts.py                 # Prompt templates (1,979 lines) ★ Core
│   ├── dispatch.py                # Agent dispatch logic (212 lines)
│   ├── commands/                  # CLI subcommands (8,585 lines total)
│   │   ├── loop.py                # Main proving loop
│   │   ├── init.py                # Project initialization
│   │   ├── dag/                   # DAG-based blueprint building
│   │   ├── dashboard/             # Web dashboard server
│   │   ├── physics_formalize.py   # Physics-specific (1,762 lines)
│   │   ├── prove.py               # Single theorem proving
│   │   └── tooling/               # Utility commands
│   ├── agents/                    # Multi-engine support
│   │   └── codex.py               # OpenAI Codex integration (44KB)
│   ├── state/                     # Loop state management
│   ├── multilane/                 # Multi-provider proving
│   ├── subagents/                 # Autonomous subagents
│   └── ui/                        # Web dashboard (TypeScript/Node.js)
│
├── Formalizer/                    # Physics problem auto-formalization (592KB)
│   ├── main.py                    # Entry point
│   ├── stage1_planner.py          # Problem decomposition
│   ├── stage2_synthesizer.py      # Lean code synthesis
│   ├── stage3_alignment.py        # Semantic verification
│   ├── modules/                   # Supporting modules
│   └── prompts/                   # LLM prompts for each stage
│
├── hipho_ipho_2024_2025/          # IPhO physics dataset (8.2MB)
│   ├── raw/                       # Raw problem data (JSON)
│   ├── image_question/            # 27 problem images
│   └── hipho_ipho_2024_2025_humanizephysics.jsonl
│
├── tests/                         # 50+ test files (804KB)
├── docs/                          # Documentation (2.5MB)
│   ├── CONFIGURATION.md
│   ├── CHANGELOG.md
│   ├── MIGRATION.md
│   └── MULTILANE.md
│
├── scripts/
│   └── run.sh                     # Quick-start script
│
├── physics_formalize.py           # Top-level physics entry (100KB)
├── physics.md                     # Physics proof workflow
├── pyproject.toml                 # Package metadata
├── install.sh                     # Installation script
├── LICENSE                        # Apache 2.0
└── THIRD_PARTY_NOTICES.md         # MIT fork attribution
```

---

## 2. What scripts/run.sh Does

```bash
#!/usr/bin/env bash
set -euo pipefail

PROJECT="${1:-/home/ma-user/Python_project/HumanizePhysicsHiphoProblemSetSmoke_20260701-224644}"
HUMANIZEPHYSICS_ROOT="${HUMANIZEPHYSICS_ROOT:-/home/ma-user/Python_project/HumanizePhysics}"

# Prepend essential tools to PATH
export PATH="/home/ma-user/.elan/bin:/home/ma-user/.local/node-v22.15.1-linux-x64/bin:..."

cd "$HUMANIZEPHYSICS_ROOT"
exec .venv/bin/humanizephysics loop "$PROJECT" \
  --from prover \
  --max-iterations "${HUMANIZEPHYSICS_MAX_ITERATIONS:-1}" \
  --max-parallel "${HUMANIZEPHYSICS_MAX_PARALLEL:-4}" \
  --max-objectives "${HUMANIZEPHYSICS_MAX_OBJECTIVES:-10}" \
  --no-dashboard
```

### Purpose
- Quick-start entry point for running HumanizePhysics's main proving loop
- Takes a Lean 4 project directory as argument (defaults to smoke test)
- Launches **prover agent** (`--from prover`) rather than planning
- Respects environment variables for parallelism/iteration limits
- Runs headless (`--no-dashboard`) for CI/automation

### Key Flags
| Flag | Purpose |
|------|---------|
| `--from prover` | Skip planning phase; go directly to proving |
| `--max-iterations` | Stop after N iterations (default 1) |
| `--max-parallel` | Run N concurrent prover agents (default 4) |
| `--max-objectives` | Prove up to N objectives/iteration (default 10) |
| `--no-dashboard` | Disable web UI; run headless |

---

## 3. Existing Documentation

### Primary Docs
1. **docs/CONFIGURATION.md** — Backend selection, harness config, model selection
2. **docs/CHANGELOG.md** — v0.3.0 features: DAG blueprints, modular engines, multilane
3. **docs/MIGRATION.md** — Upgrade from v0.2.0 → v0.3.0
4. **docs/MULTILANE.md** — Parallel multi-provider proving
5. **physics.md** — Physics proof workflow guide

**No primary README** — typical entrypoint is `humanizephysics --help`

---

## 4. Key Source Files & Purpose

### Core Infrastructure
| File | Lines | Purpose |
|------|-------|---------|
| `agent.py` | 1,950 | ★ Wraps `claude` CLI; centralizes model selection & logging |
| `prompts.py` | 1,979 | ★ Prompt templates for all roles (plan, prover, review) |
| `dispatch.py` | 212 | Routes work to harnesses; selects backend/engine per role |
| `commands/loop.py` | — | Main iteration loop: plan → prove → review |
| `commands/physics_formalize.py` | 1,762 | Auto-formalize physics problems |

### Proof Loop & State
- `state/progress.py` — Iteration tracking
- `state/iteration.py` — Per-iteration snapshots
- `state/cost.py` — Token/cost accounting

### Physics Formalization
- `Formalizer/stage1_planner.py` — Problem decomposition
- `Formalizer/stage2_synthesizer.py` — Lean synthesis
- `Formalizer/stage3_alignment.py` — Semantic verification
- `Formalizer/modules/llm_modules.py` — LLM integration

### Multi-Engine Support
- `agents/codex.py` — OpenAI Codex integration (44KB)
- `multilane/` — Parallel proving across providers

### Web Dashboard
- `ui/server/` — Express.js backend
- `ui/client/` — Vite/Vue.js frontend

---

## 5. Configuration Files

| File | Purpose |
|------|---------|
| `pyproject.toml` | Package metadata, dependencies, entry points |
| `.humanizephysics/config.json` | Per-project loop settings (harness, model, backend) |
| `.humanizephysics/AGENTS.md` | Role documentation (loaded by all engines) |
| `.humanizephysics-protected.yaml` | Protection rules for Lean files & blueprints |
| `src/humanizephysics/.humanizephysics-src/prompts/` | Default prompt templates |
| `src/humanizephysics/.humanizephysics-src/subagents/` | Subagent specifications |
| `Formalizer/prompts/` | Physics-specific LLM prompts (15 files) |

---

## 6. Language & Framework

### Core Stack
- **Python 3.10+** (specified in pyproject.toml)
- **Typer** — Modern Python CLI framework
- **Click** — CLI utilities
- **Pydantic** — Data validation & serialization

### LLM Integration
- **Claude Code CLI** (`claude`) — Anthropic's headless orchestrator
- **OpenAI SDK** — For Codex/GPT endpoints
- Custom harness system for engine abstraction

### Lean 4 Integration
- **lean-explore** — Semantic search over Lean definitions
- **leandag @ v0.1.0** — Dependency graph analysis
- **claude-p @ v0.1.5** — Interactive TUI wrapper

### Data & Config
- **PyYAML** — YAML parsing
- **Pillow** — Image handling (physics problems)

### Testing
- **pytest** — 50+ test modules

### Web Dashboard
- **Node.js v22.15.1** — Runtime
- **TypeScript** — Type-safe backend
- **Express.js** — Web server
- **Vite** — Vue.js build tooling

### External Tools
- **Lean 4** — Proof assistant (via elan)
- **elan** — Lean toolchain manager

---

## 7. Dockerfile / Docker Compose

**None found.** Project assumes:
- Local Python 3.10+ with venv
- Lean 4 via elan
- Node.js 22 for dashboard
- Installed via `install.sh`

---

## 8. Project Size Breakdown

| Component | Size |
|-----------|------|
| `src/humanizephysics/` | 54MB |
| `hipho_ipho_2024_2025/` | 8.2MB |
| `docs/` | 2.5MB |
| `tests/` | 804KB |
| `Formalizer/` | 592KB |
| **Total** | ~66MB |

---

## 9. Key Development Artifacts

### Test Coverage
- 50+ test files covering agent lifecycle, initialization, multilane, physics, DAG ops
- Examples: `test_agent_bash_timeout.py`, `test_multilane.py`, `test_physics_formalize.py`

### Prompt Templates (`.humanizephysics-src/prompts/`)
- `plan.md` — Blueprint planning
- `prover-*.md` — Proof tactics (formalize, prove, polish, golf)
- `review.md` — Proof review
- `discuss.md` — Interactive guidance

### Subagent Specs (`.humanizephysics-src/subagents/`)
- `lean-scaffolder.md`, `mathlib-analogist.md`, `blueprint-reviewer.md`, etc. (12+ agents)

---

## 10. Main Workflow

```
humanizephysics loop <project>
    ↓
Phase 1: Plan (create objectives from blueprint)
    ↓
Phase 2: Prover (prove objectives in parallel)
    ↓
Phase 3: Review (refine proofs)
    ↓
Phase 4: Iterate (repeat)
    ↓
Output: Verified Lean code + logs
```

---

## 11. Important Notes

### Version
- **0.3.1** (current)
- Major features: DAG blueprints, modular harnesses, multilane proving

### License
- **Apache 2.0** (primary)
- MIT for bundled forks

### Architecture Highlights
- One-shot headless agent model (each phase is `claude -p` subprocess)
- Blocking subagent dispatch maintains turn atomicity
- JSONL logging for all activity
- Harness abstraction for Claude ↔ Codex swapping
- DAG-grounded planning (v0.3.0+) uses real Lean dependency graph

### Critical Files
- `agent.py` — All agent invocation goes through `ClaudeAgent.run()`
- `prompts.py` — Central prompt repository
- `.humanizephysics/AGENTS.md` — Shared role documentation

---

## Summary

| Aspect | Details |
|--------|---------|
| **Primary Language** | Python 3.10+ |
| **CLI Framework** | Typer |
| **Purpose** | Autonomous Lean 4 theorem formalization via AI |
| **AI Engines** | Claude Code (Anthropic), OpenAI Codex |
| **Proof Assistant** | Lean 4 (via elan) |
| **Dashboard** | Node.js + TypeScript + Vite/Vue.js |
| **License** | Apache 2.0 |
| **Version** | 0.3.1 |
| **Docker Support** | None (system packages) |
| **Install Method** | `bash install.sh` or `pip install .` |

