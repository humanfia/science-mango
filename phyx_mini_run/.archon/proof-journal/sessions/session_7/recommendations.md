# Iter-008 Recommendations

## Blockers first

- Global physics review remains BLOCKED:
  - `PhyXMiniProblems/problem_phyx_mini_0206.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
  - `PhyXMiniProblems/problem_phyx_mini_0472.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
- Route `0206`/`0472` through an authorized structural Lean-writing lane; do not ordinary-prover dispatch them.
- Repair current grounding evidence for the 35 missing-report targets and refresh stale `0117`/`0629` reports before proof dispatch. Generic preflights are insufficient.

## Next proof wave

- Do not reassign `0005`, `0340`, `0402`, `0792`, `0882`, or `0922`; all are proof-closed and target-level physics-audited.
- Select the next batch only from the 941 gate-passed open files. Prefer one-sorry algebraic targets whose blueprint has a real derivation; short one-sorry files with generic autoformalization prose first need planner prose replacement.
- The iter-005 optics targets `0007`, `0008`, `0016`, `0017` remained open after a full `physics` pass. Do not retry the same monolithic approach; use `fine-grained`/decomposition first if selecting them.
- Reusable low-risk lane: common endpoints + the same state law (`0340`); specialize scalar readouts, rewrite, then `linarith`.
- Reusable work lane: rewrite per-segment laws and calibrated coordinates, then exact `norm_num` (`0402`).
- Reusable field/linkage lane: derive intermediate products, prove denominator/current nonzero explicitly, cancel, then `ring` (`0922`).

## Reusable Lean details

- Acute trig contradiction (`0005`): use `Real.tan_eq_sin_div_cos`, positivity from acute intervals, `field_simp`, and finish against `Real.sin_sq_add_cos_sq`.
- Euclidean cross product (`0792`): get x from `InnerProductGeometry.cos_angle_mul_norm_mul_norm`; use `EuclideanSpace.real_norm_sq_eq` plus orientation positivity for y; evaluate with `cross_apply`.
- Physlib `Time` limits (`0882`): locally provide `IsDirectedOrder Time` using coordinatewise `max`, with explicit `change` goals before `le_max_left/right`; then `tendsto_nhds_unique` is available.

## Doctor, graph, and controls

- Doctor structural findings: 0 orphans, broken/malformed refs, and axioms; `physics_grounding_problems=[]`.
- Current leandag: gaps 0, unmatched 0; no coverage repair is required for iter-007.
- Restore run-local `.archon/AGENTS.md` and `.archon/prompts/{plan,review}.md` from the known identical-SHA canonical copies through an authorized control-file route.
- Marker sync will likely remove manual target markers again until standalone generated modules are registered or sync supports direct-file checks; preserve the reviewed overrides.
