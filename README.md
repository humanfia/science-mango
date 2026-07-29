# Science Mango Ipho 2026 K3 Run

<!-- archon:readme -->

## Project

An isolated Archon run that formalizes all 28 IPhO 2026 targets with Moonshot
K3 (`biui-0724`) through the OpenAI-compatible Chat Completions API. Each
target has its own worker and Lean file.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `IPhO2026Run/` — main Lean source
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
scripts/start_ipho_2026_k3.sh --resume
scripts/status_ipho_2026_k3.sh
```

The launcher validates the pinned Codex Chat harness, starts the local
compatibility proxy and LeanExplore endpoint, then runs 28 target workers.
Secrets and Archon runtime state remain under the ignored `.archon/` directory.
