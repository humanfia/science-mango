# Iteration 002 Plan

## Decision made

- Dispatch all 527 review retries. Project overrides (`max_objectives=1000`,
  `max_parallel=32`) make one broad repair wave feasible and the three-review
  ceiling makes ten-file batching too slow. Cost: roughly 5k–25k Lean LOC;
  risk: heterogeneous lane quality. Reverse only if validation reports runaway
  fan-out or systematic unchanged reasons.
- For `0016`, follow the primary image and Snell laws: formalize choice B
  ($27.5^\circ$), retaining recorded C only as metadata. Reverse only on a
  source showing a different angle convention.

## Doctor and graph handling

- All 237 import/library blockers are dispatched with explicit Mathlib/Physlib
  grounding requirements; 162 evidence gaps and 128 semantic defects are also
  dispatched under their exact gate reasons.
- Added unique target links for all 473 passed files; unmatched declarations
  fell 31,436 → 30,963. Remaining target/helper linkage is deferred until the
  527 redrafts stabilize names; premature blocks would immediately become
  stale. This deferral is an explicit topology phase in `STRATEGY.md`.

## Tool substitutions

- Run-local role/prompt files were absent; used identical-SHA canonical
  archive/template copies. No subagents were enabled or invoked.
- Processed task reports were retained because the plan role cannot edit
  `task_results/`.
