# HumanizePhysics

**Autonomous Lean 4 Formalization System** — Automatically transforms mathematical theorems and physics problems into verified Lean 4 formal proofs.

HumanizePhysics uses an AI-powered (Claude / OpenAI Codex) multi-stage pipeline to automate the entire process from natural-language problems to machine-verifiable Lean 4 proofs.

---

## Table of Contents

- [Quick Start](#quick-start)
- [Launch Script](#launch-script-scriptsrunsh)
- [Environment Variables](#configurable-environment-variables)
- [Project Structure](#project-structure)
- [Technology Stack](#technology-stack)
- [Common Commands](#common-commands)
- [Documentation](#documentation)

---

## Quick Start

```bash
# 1. Install system dependencies (Lean 4, elan, Node.js, etc.)
humanizephysics setup

# 2. Initialize a project directory
humanizephysics init <project-dir>

# 3. Start the proof loop
scripts/run.sh <project-dir>
```

---

## Launch Script (`scripts/run.sh`)

`scripts/run.sh` is the **one-command launch entry point** for HumanizePhysics. It is designed for unattended batch proving scenarios such as CI, remote servers, and scheduled jobs.

### Usage

```bash
# Start using the default project path
./scripts/run.sh

# Start with a specified project directory
./scripts/run.sh /path/to/your/project
```

### What the Script Does

1. **Configures `PATH`** — Adds `elan` (the Lean toolchain manager), `Node.js v22`, and `npm` to `PATH` to ensure a complete runtime environment.
2. **Changes to the HumanizePhysics root directory** — Enters `$HUMANIZEPHYSICS_ROOT` (default: `/home/ma-user/Python_project/HumanizePhysics`).
3. **Runs the proof loop** — Invokes `humanizephysics loop` in **prover-only** mode (`--from prover`), skipping the preceding formalization and extraction stages and proceeding directly to proof solving.
4. **Runs without the Dashboard** — Uses `--no-dashboard` for a command-line-only workflow suitable for headless servers.

### Configurable Environment Variables

| Variable | Default | Description |
|---|---|---|
| `HUMANIZEPHYSICS_ROOT` | `/home/ma-user/Python_project/HumanizePhysics` | HumanizePhysics installation root directory |
| `HUMANIZEPHYSICS_MAX_ITERATIONS` | `1` | Maximum number of proof iterations per objective |
| `HUMANIZEPHYSICS_MAX_PARALLEL` | `4` | Number of objectives proved concurrently |
| `HUMANIZEPHYSICS_MAX_OBJECTIVES` | `10` | Maximum number of objectives processed in a single run |

**Example: High-concurrency run**

```bash
HUMANIZEPHYSICS_MAX_PARALLEL=8 HUMANIZEPHYSICS_MAX_ITERATIONS=3 HUMANIZEPHYSICS_MAX_OBJECTIVES=50 \
  ./scripts/run.sh /path/to/project
```

---

## Project Structure

```
HumanizePhysics/
├── scripts/
│   └── run.sh                   # ⭐ Launch script (entry point)
├── src/humanizephysics/
│   ├── cli.py                   # CLI entry point (Typer)
│   ├── agent.py                 # AI agent wrapper (Claude CLI)
│   ├── prompts.py               # Prompt templates
│   ├── dispatch.py              # Harness routing (Claude / Codex)
│   ├── log.py                   # Logging system
│   ├── types.py                 # Type definitions (Pydantic)
│   └── commands/
│       ├── loop/                # Main proof-loop orchestration
│       ├── prove.py             # Single-objective proving
│       ├── physics_formalize.py # Automated physics problem formalization
│       ├── setup/               # Dependency installation
│       ├── init/                # Project initialization
│       └── ...
├── docs/                        # Documentation
├── tests/                       # Tests (pytest)
├── pyproject.toml               # Package metadata and dependencies
└── .venv/                       # Python virtual environment
```

---

## Technology Stack

| Layer | Technology |
|---|---|
| Language | Python 3.10+ |
| CLI framework | Typer + Click |
| AI backends | Claude Code CLI, OpenAI SDK |
| Theorem prover | Lean 4 (via elan) |
| Dependency graph analysis | leandag, lean-explore |
| Dashboard | Node.js 22 + Express + Vue.js |
| Data validation | Pydantic |
| Testing | pytest |

---

## Common Commands

```bash
humanizephysics setup              # Install system dependencies (elan, Node.js, etc.)
humanizephysics init <dir>         # Initialize a project directory
humanizephysics loop <dir>         # Start the proof loop
humanizephysics prove <file>       # Run the prover on a single file
humanizephysics doctor             # Check whether the environment is ready
humanizephysics dashboard          # Start the web dashboard
humanizephysics --help             # Show all commands
```

---

## Documentation

- [CONFIGURATION.md](docs/CONFIGURATION.md) — Detailed project configuration
- [MULTILANE.md](docs/MULTILANE.md) — Parallel proving across multiple lanes
- [MIGRATION.md](docs/MIGRATION.md) — Version migration guide
- [CHANGELOG.md](docs/CHANGELOG.md) — Changelog

---

## License

See the project's license file for details.
