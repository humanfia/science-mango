# IPhO 2026 run results

Snapshot date: 2026-07-27 (UTC)

| Metric | Result |
|---|---:|
| Total targets | 28 |
| Formalization Review passed (legacy schema) | 28 |
| Proof Review passed | 25 |
| Lean files with an active `sorry` | 2 |
| Semantically unresolved targets | 3 |
| Final `lake build` | Passed |

## Unresolved targets

| Target | Lean status | Review diagnosis |
|---|---|---|
| `1_B_2` | One `sorry` in `signed_deflection_formula` | The contract lacks a governing-law projection connecting the limiting velocity to the signed outgoing hyperbolic branch. |
| `2_B_1` | One `sorry` in `radiusAtIncidence_from_figure2f` | The limiting/tangency predicates expose no elimination law deriving the required radius formula. |
| `4_B_6` | Placeholder-free and compiling | Later semantic Review found that the target conclusion does not encode uncertainty propagation. |

The first two failures are proof-stage observations whose root cause is an
insufficient formalization contract. They should be routed through the newer
`needs_redraft` proof Review path before another proof attempt. The saved gate
files predate that routing schema and therefore record all three as
`proof_review_exhausted`.

## Saved evidence

- `reports/final/`: final progress, gate state, and project knowledge base.
- `reports/archon_task_results/`: per-target grounding and prover reports.
- `reports/source/`: source-extraction reports used to construct each target.
