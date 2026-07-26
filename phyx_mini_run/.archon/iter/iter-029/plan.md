# Iteration 029 Plan

## Decision made

- Dispatch zero objectives. The installed Archon selector returns 0 candidates:
  963 formalization-passed files partition into 933 proof-solved, 24
  `proof_review_exhausted`, and six earlier certified closed files outside
  proof-gate tracking. Those six have zero placeholders. Thus accepted-open
  targets are 0, `min(32, 0) = 0`, and the exact eligibility shortfall is 32.
- Reverse only after an authorized structural repair changes a gate status and
  restores a live accepted-open target. Dispatching any present placeholder
  would violate the prohibition on exhausted targets.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: both require Lean edits,
  plan has no Lean write authority, and structural subagents are disabled.
- No infinite-effort source, broken `\uses{}` reference, or coverage debt
  exists. The 29 isolated nodes remain audited dead; cleanup needs coordinated
  Lean/blueprint deletion, while invented dependency edges would be false.

## State and tool substitution

- No prover result is newer than the iteration-028 planning state.
- Run-local role files remain absent; used canonical archive copies whose
  hashes match the Archon template copies.
