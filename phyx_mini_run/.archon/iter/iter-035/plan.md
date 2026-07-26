# Iteration 035 Plan

## Decision made

- Dispatch zero objectives. The installed deterministic selector returns 0
  candidates at limits 32 and 128: 963 formalization-passed files partition
  into 933 proof-solved, 24 `proof_review_exhausted`, and six earlier
  certified closed files outside proof-gate tracking. Each legacy file has
  zero placeholders. Thus accepted-open targets are 0, `min(32, 0) = 0`, and
  the exact eligibility shortfall is 32.
- Reverse only when an authorized structural repair plus explicit gate reset
  restores a passed, non-exhausted open target. Plan cannot spend the
  estimated 200--4,000 LOC repair budget by editing Lean itself.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: both require Lean edits,
  and structural subagents remain disabled.
- No infinite-effort source, broken `\uses{}` reference, or coverage debt
  exists. The 29 isolated nodes are audited dead; blueprint-only deletion
  would create unmatched Lean debt, while invented edges would be false.

## State and tool substitution

- Session 34 reviewed zero targets, requested no retries, and produced no new
  prover result.
- Run-local role files remain absent; identical-SHA canonical archive copies
  supplied the instructions.
