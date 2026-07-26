# Strategy

## Goal

Produce faithful, compiling Lean/PhysLean statements for all 1,000 PhyX-mini
problems, pass the formalization review gate, close every proof obligation,
and polish the corpus without weakening any physical claim.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
| --- | --- | ---: | ---: | --- | --- |
| Proof-exhausted statement repair | BLOCKED | 2–8 | ~200–4,000 | Faithful hypotheses; direct elaboration | 24 targets cannot be redispatched without structural repair and gate reset |
| Gate-failed evidence/import repair | BLOCKED | 1–3 | ~100–2,000 | Direct imports; current grounding reports | 35 missing reports, 2 stale reports, and 2 import defects need an authorized route |
| Repaired-target physics proofs | NEXT | 2–8 | ~500–5,000 | Depends on repair outcomes | Up to 61 repaired files; proof gates must be reset explicitly |
| Isolated declaration cleanup | NEXT | 1 | ~50–200 | Structural Lean edit capability | 29 dead nodes; false dependency edges forbidden |
| Corpus polish | NEXT | 1–2 | ~2,000–8,000 | Standard idioms and dependency minimization | Large heterogeneous corpus; regression cost |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
| --- | --- | ---: | --- | --- | --- | --- |
| Initial physics scaffolding | 001 · 1 | ~31,000 declarations | 1,000 Lean files and chapters | All targets elaborate | Typed roles plus explicit scalar projections; separate laws/readouts/targets | Compilation alone hid grounding/model failures |
| Lean–blueprint coverage baseline | 003 · 1 | ~269,000 TeX lines | 1,001 chapters | Lean-to-blueprint unmatched debt cleared | Derive direct edges from declaration references | Public-name churn requires resync; never invent edges for dead helpers |
| Formalization review and recovery | 006 · 5 | ~5,000–25,000 | 1,000 targets | 963 passed; 37 await evidence/import repair | Symbolic strongest-supported targets for missing data | Generic preflights and stale reports are not certification |
| Review-safe accepted proofs | 023 · 19 | proof-local | 939 files | 933 proof-Review solved plus 6 earlier certified closed | Scalarization, exact laws before bounds, explicit branch conditions | 24 under-hypothesized or non-elaborating targets exhausted Review |

## Routes

Single route: structurally repair and reset the 24 proof-exhausted targets,
repair and certify the 37 formalization-exhausted statements through an
authorized evidence/import route, prove the repaired set, remove dead
declarations, and polish. When metadata conflicts with the primary image and
governing laws, retain it as metadata but formalize only the physically
supported conclusion.

## Open key strategic questions

- Which target-determining calibration values can be traced to an original source rather than retained as explicit conditional assumptions?
- Which proof families need reusable certified transcendental bounds rather than problem-local numerical automation?
- Which numerical conclusions need certified interval bounds rather than decimal tolerances alone?

## Mathlib gaps & new material

### Gaps to fill

- Geometrical-optics interfaces for refractive index, Snell refraction, critical incidence, and ray reflection.
- Reusable dimensional models for thermodynamic, electromagnetic, and laboratory readouts.
- Certified transcendental estimates for multiple-choice rounding obligations.

### New project material

- Typed problem-local media, apparatus, figure labels, ray/state records, and governing-law interfaces.
- Local derivative, limit, asymptotic, neighborhood, and remainder contracts for approximation claims.
