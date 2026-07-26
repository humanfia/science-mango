# Iteration 031 Plan

## Decision made

- Dispatch zero objectives. The installed Archon selector returns 0 candidates
  at limits 32 and 128: 963 formalization-passed files partition into 933
  proof-solved, 24 `proof_review_exhausted`, and six earlier certified closed
  files outside proof-gate tracking. The six have no live placeholder.
  Therefore accepted-open targets are 0, `min(32, 0) = 0`, and the exact
  eligibility shortfall is 32.
- Reverse only after an authorized structural repair changes a gate status and
  restores a live accepted-open target. Dispatching any current frontier
  placeholder would select an exhausted target.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: both require Lean edits,
  plan has no Lean write authority, and structural subagents are disabled.
- No infinite-effort source, broken `\uses{}` reference, or coverage debt
  exists. The 29 isolated nodes remain audited dead; cleanup requires
  coordinated Lean/blueprint deletion, while invented dependency edges would
  be false.

## State and tool substitution

- Session 30 reviewed zero targets; no new prover result exists.
- Run-local `AGENTS.md` and plan prompt remain absent; their canonical copies
  match across archive, sibling runs, and installed templates by SHA-256.
