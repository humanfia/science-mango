# IChO 2026 Lean run

## Status

This Lake project contains formalizations and proofs for the 32
`formalization_ready` theory subquestions from IChO 2026 papers T1--T9.
The practical/experimental papers P1--P3 are intentionally excluded.

As of 2026-08-11, all 32 theory targets have compiled proofs, hash-bound
source-aware formalization Review certificates, and source-aware proof Review
certificates. Their source files contain no `sorry`, `admit`, `sorryAx`, or
local `axiom` declarations.

| Paper | Verified targets |
| --- | ---: |
| T1 | 2 |
| T2 | 3 |
| T3 | 4 |
| T4 | 7 |
| T5 | 3 |
| T6 | 3 |
| T7 | 2 |
| T8 | 3 |
| T9 | 5 |

The strengthened Review pass binds every certificate to the official question,
rubric answer, previous parts, every source image, and the current Lean and
blueprint hashes. It found and forced repairs to the T1-A3 isotope-reporting
contract, the T5-A4 reagent domain, the T6-A4 ion-assignment scope, and the
T9-A6 regioisomer branch before the final 32/32 result was accepted.

The project pins Lean 4.31.0, Mathlib, Physlib, and `crnt-lean`.

## Shared chemistry infrastructure

The shared-infrastructure workflow generated
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

## Reproduce the build

Run these commands from this directory.

```bash
# Fetch dependencies/cached oleans and compile the shared module plus all 32
# problem modules through the umbrella import.
lake exe cache get
lake build

# Rebuild the local Chemistry overlay, then start the composite MCP service.
./scripts/rebuild_lean_explore_index.sh
./scripts/start_lean_explore.sh

```

`start_lean_explore.sh` is idempotent and reports the existing PID when the
service is already running.

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

See `references/summary.md` for source-material notes and
`reports/icho_2026/pilot-summary.md` for the detailed verified checkpoint.
