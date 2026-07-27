# Strategy

## Goal

Complete faithful typed Lean/PhysLean formalizations and axiom-clean proofs for the 22 IPhO 2026 theory targets. Keep the six experimental E1 targets explicitly user-skipped until the user resumes them.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
| --- | --- | ---: | ---: | --- | --- |
| Polish and verify all 22 theory files | ACTIVE | 3 | ~100–500 | Simplification and import hygiene | Preserve reviewed physics contracts |
| Six experimental E1 targets | PAUSED BY USER | — | ~250–900 | Physlib dimensions and uncertainty carriers | Resume only on explicit user direction |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
| --- | --- | ---: | --- | --- | --- | --- |
| Init and source extraction | pre-001 · n/a | n/a | 28 reports and chapters | Source-backed target per selected part | Official page image plus per-part JSON | Previous parts are prose inputs only |
| Typed statement scaffolds for theory | 002 · 2 | n/a | 22 theory files | Physics-aware contracts compile | Dimensionful lengths plus named SI projections | One valid-looking helper lacked positivity |
| Proof Review-accepted theory proofs | 003 · 1 | ~3,000 | 20 theory files | 20 targets closed axiom-clean | Branch conditions, exact algebra, local asymptotics | Answer-bearing assumptions can hide unused physics |
| Rejected-contract repair and closure | 005 · 2 | +23 net | `1_C_1`, `2_B_1` | C.1 validity and B.1 tangency contracts closed axiom-clean | Positive scalar magnitudes; derive coefficients from geometry | Do not infer positivity from a “magnitude” field |

## Routes

Single active theory route: polish the 22 Proof Review-accepted theory targets in bounded batches, preserving every reviewed contract. Experimental E1 remains paused by user.

## Open key strategic questions

- None; all 22 theory contracts are Proof Review-accepted.

## Mathlib gaps & new material

### Gaps to fill

- No current theory blocker requires new Mathlib infrastructure.

### New project material

- Local typed models for conservation laws, optics, thermodynamics, and asymptotic approximations.
- Physlib-backed length carriers with named SI projections where analytic coordinates are scalar.
