# IChO 2026 Lean run

## Status

This Lake project runs Archon's chemistry formalization and proof workflow on
the 32 `formalization_ready` theory subquestions from IChO 2026 papers T1--T9.
The practical/experimental papers P1--P3 are intentionally excluded.

As of 2026-08-10, six theory targets have compiled proofs and semantic Review
certificates. Their source files contain no `sorry`, `admit`, `sorryAx`, or
local `axiom` declarations:

| Target | Verified result |
| --- | --- |
| T2-A2 | Stationary HBrO2 concentrations: `6.0e-6 M` in Process A and `5.04e-11 M` in Process B |
| T2-A3 | Critical bromide concentration: `3.0e-7 M` |
| T2-A5 | Exact first-order period formulas, with nearest-second results `48 s` for the official branch and `37 s` for the source-authorized fallback |
| T4-A5 | Exact logarithmic collision-count formula, certified `19.97` readout and nearest integer `20` |
| T4-A6 | Standard methane-combustion enthalpy at 298 K: `-802.3 kJ mol⁻¹` |
| T4-A7 | Constant-heat-capacity result at 2000 K: `-781.876 kJ mol⁻¹`, with the rounding guarantee for `-781.9` |

The project pins Lean 4.31.0, Mathlib, Physlib, and `crnt-lean`.

## Shared chemistry infrastructure

Archon's shared-infrastructure workflow generated
`IChO2026Chem/Kinetics/BelousovZhabotinsky.lean`, reviewed it, and migrated
T2-A2, T2-A3, and T2-A5 to the common species, state, kinetic-parameter, and
mass-action-rate definitions. The shared module and all three consumer
migrations were build- and axiom-verified before the queue was marked
resolved.

## LeanExplore

The configured search packages are `Mathlib`, `Physlib`, and `Chemistry`.
The local service on port 8765 combines hosted LeanExplore search for
Mathlib/Physlib with a project overlay named `Chemistry`. The overlay is built
from `IChO2026Chem/` and the pinned CRNT sources, so newly shared chemistry
declarations and CRNT declarations are searchable without locally indexing all
of Mathlib and Physlib.

## Portable Archon configuration

`.archon/config.json` is the portable, trackable exception under the otherwise
ignored `.archon/` runtime directory. It records the chemistry domain profile,
formalization and proof Review gates, shared-infrastructure policy, Codex
harness, and hosted-plus-overlay LeanExplore endpoint. Credentials belong only
in `.archon/.env` and must not be committed.

## Reproduce the build and loop

Run these commands from this directory. The helper scripts expect the Archon
virtual environment at `../.venv`.

On a fresh checkout, materialize Archon's ignored runtime prompts and state
once. The committed chemistry configuration is preserved; the init pass is
interactive and asks you to confirm its proposed objectives.

```bash
../.venv/bin/archon init .
```

```bash
# Fetch dependencies/cached oleans and compile the shared module plus all six
# problem modules through the umbrella import.
lake exe cache get
lake build

# Rebuild the local Chemistry overlay, then start the composite MCP service.
./scripts/rebuild_lean_explore_index.sh
./scripts/start_lean_explore.sh

# Run plan -> prove -> Review using .archon/config.json.
../.venv/bin/archon loop .
```

`start_lean_explore.sh` is idempotent and reports the existing PID when the
service is already running. Its log and PID file are written under
`.archon/runtime/`.

To repeat the source-level placeholder check:

```bash
rg -n '\b(sorry|admit|axiom|sorryAx)\b' IChO2026Chem IChO2026Problems
```

A clean run prints no matches. The blueprint can be rebuilt separately with
`leanblueprint pdf` and `leanblueprint web` from `blueprint/`.

## Project layout

- `IChO2026Chem/` -- reviewed shared chemistry infrastructure
- `IChO2026Problems/` -- generated, reviewed, and proved problem modules
- `IChO2026Run/` -- dependency probes and the default build root
- `blueprint/` -- leanblueprint sources
- `references/` -- the 32-entry theory queue and batch shards
- `reports/icho_2026/` -- source manifests and the stable checkpoint summary
- `scripts/` -- theory selection and LeanExplore overlay helpers
- `archon-protected.yaml` -- optional protected-surface policy template
- `.archon/config.json` -- trackable run configuration; other `.archon` files are runtime state

See `references/summary.md` for source-material notes and
`reports/icho_2026/pilot-summary.md` for the detailed verified checkpoint.
