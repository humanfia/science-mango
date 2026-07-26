# Iteration 033 Plan

## Decision made

- Dispatch zero objectives. The installed deterministic selector returns 0
  candidates at limits 32 and 128: 963 formalization-passed files partition
  into 933 proof-solved, 24 `proof_review_exhausted`, and six earlier
  certified closed files outside proof-gate tracking. Each of those six has
  zero placeholders. Thus accepted-open targets are 0, `min(32, 0) = 0`, and
  the exact eligibility shortfall is 32.
- Do not use the estimated 200--4,000 LOC structural-repair route without an
  authorized Lean writer. Reverse when an authorized repair plus explicit
  gate reset restores a passed, non-exhausted open target.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: both require Lean edits,
  while plan cannot edit Lean and structural subagents remain disabled.
- No infinite-effort source, broken `\uses{}` reference, or coverage debt
  exists. The 29 isolated nodes are audited dead; deleting only blueprint
  blocks would create unmatched Lean debt, while invented edges would be
  false.

## State and tool substitution

- Session 32 reviewed zero targets and requested no retries.
- Run-local role files remain absent; canonical archive copies match sibling
  runs by SHA-256 and supplied the instructions.
