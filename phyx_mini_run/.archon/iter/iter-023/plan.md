# Iteration 023 Plan

## Decision made

- Dispatch zero objectives. The deterministic intersection is empty:
  formalization `passed`, live placeholder, and proof status neither `solved`
  nor `proof_review_exhausted` has 0 files. Thus `min(32, 0) = 0`; exact
  eligibility shortfall is 32. Redispatching any of the 24 exhausted targets
  would violate the standing directive.
- Split the remaining arc into 24 proof-exhausted structural repairs and 37
  formalization-gate repairs. Expected repair cost is ~300–6,000 LOC; the
  cheaper but unsound alternative is bypassing frozen missing hypotheses.
  Reverse this no-dispatch decision only when a gate changes after authorized
  redraft/re-review.

## Doctor and graph handling

- The frontier has 143 nodes and 39 live-placeholder files: 30 formalization
  exhausted and 9 proof exhausted. No eligible frontier file exists.
- Deferred `0206`/`0472` direct-`Mathlib` imports: both are Lean edits outside
  plan authority, and subagents are disabled. No blueprint edit can repair an
  import defect.

## Tool substitution

- Run-local role files are absent; used their identical-SHA archive copies and
  the project-venv Archon CLI.
