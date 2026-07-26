# Prover result: `problem_phyx_mini_0080.lean`

## Status

Complete. The current assigned Lean file already contains sound proofs of all
three declarations that originally had `sorry` placeholders. No declaration
signature or proof body needed to change in iteration 014.

This retry repairs the evidence-path blocker identified by proof Review: the
result is now present at the required nested path
`.archon/task_results/PhyXMiniProblems/problem_phyx_mini_0080.lean.md`.

## Proof summary

- `bragg_glancing_angle_eq_eighteen_point_eight_degrees` rewrites the stated
  `63.8°` incidence and `45°` diagonal-plane inclination into the figure's
  glancing-angle definition and proves their difference is `18.8°` in
  `Real.Angle`.
- `unit_cell_size_nanometers_formula` specializes the diagonal-spacing and
  Bragg laws to nanometres, uses first order and the positive physical branch,
  and derives `a₀ = λ / (√2 sin φ)`.
- `problem_phyx_mini_0080` certifies rational bounds for `π`, propagates them
  through sine bounds and two triple-angle identities, and obtains
  `0.5695 ≤ a₀ < 0.5705`. This proves both
  `round (1000 * a₀) = 570` and that answer C is strictly closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0080.lean` succeeded with
  no output.
- Lean LSP diagnostics: none.
- Source scan: no `sorry`, `admit`, `native_decide`, or added `axiom`; there is
  no file-specific `/- USER: ... -/` comment.
- `lean_verify` found no suspicious source patterns. The final theorem uses
  only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint

The three proved declarations are ready for `\leanok`. The blueprint was not
edited because this prover's explicit write permissions are limited to the
assigned Lean file and this task-result report.

## Redraft needed

None.
