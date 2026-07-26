# Iteration 025 Plan

## Decision made

- Dispatch zero objectives. The gate partition is unchanged: 963
  formalization-passed files equal 933 proof-solved, 24
  `proof_review_exhausted`, and six earlier certified closed files outside
  proof-gate tracking. Accepted-open targets are therefore 0, so
  `min(32, 0) = 0`; exact eligibility shortfall: 32.
- Reverse only after an authorized structural repair changes a gate status and
  restores a live accepted-open target. Dispatching a current frontier file
  would necessarily select an exhausted target.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: they require Lean edits,
  plan has no Lean write authority, and the user-selected classic loop has no
  enabled structural subagent.
- The 143-node frontier does not override file gates. There are no infinite
  effort sources, broken `\uses{}` references, or coverage debt. The 29
  isolated nodes are audited dead; removing them requires coordinated Lean
  and blueprint cleanup, while invented dependency edges would be false.

## Tool substitution

- Run-local role files remain absent; used the canonical archive copies whose
  SHA-256 values match the project-family copies.
