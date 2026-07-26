# Iteration 032 Plan

## Decision made

- Dispatch zero objectives. The installed deterministic selector returns 0
  candidates at limits 32 and 128: 963 formalization-passed files partition
  into 933 proof-solved, 24 `proof_review_exhausted`, and six earlier
  certified closed files outside proof-gate tracking. Those six have no live
  placeholder. Therefore accepted-open targets are 0, `min(32, 0) = 0`, and
  the exact eligibility shortfall is 32.
- Do not spend the estimated 200--4,000 LOC structural-repair budget through
  an unauthorized lane: plan cannot edit Lean and all structural subagents
  are disabled. Reverse when an authorized repair and explicit gate reset
  restores a passed, non-exhausted open target.

## Doctor and graph handling

- Defer the `0206`/`0472` direct-`Mathlib` imports: both require Lean edits
  outside plan authority, with no enabled structural subagent.
- No infinite-effort source, broken `\uses{}` reference, or coverage debt
  exists. The 29 isolated nodes are audited dead; deleting only their
  blueprint blocks would create unmatched Lean debt, while invented edges
  would be false.

## State and tool substitution

- Session 31 reviewed zero targets; no newer prover result exists.
- Run-local role files remain absent; used canonical archive copies whose
  SHA-256 hashes match sibling runs and installed templates.
