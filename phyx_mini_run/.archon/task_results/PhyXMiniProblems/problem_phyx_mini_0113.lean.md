# `PhyXMiniProblems/problem_phyx_mini_0113.lean`

## Summary

- Sorry count: 1 → 0.
- Closed:
  `PhyXMiniProblems.ProblemPhyXMini0113.object_distance_matches_choice_A`.
- Remaining sorries: none.
- No adjacent sorries existed in the assigned file.
- No declarations, axioms, or imports were added.

## `object_distance_matches_choice_A`

- **Result:** RESOLVED.
- **Approach:** Used Physlib's
  `CarriesDimension.toDimensionful_apply_apply` to normalize the stated
  `4.00 mm` and `8.00 mm` dimensionful heights. The inverted-orientation
  sign and height magnification law then give `m = -2`.
- The Figure 113 intercept and calibration-line hypothesis give the mirror
  focal readout `f = 25 cm`.
- Positivity of the dimensionful object distance supplies the nonzero
  denominator needed to rewrite `m = -s'/s` as `s' = 2s`.
- Substitution into `1/s + 1/s' = 1/f`, followed by `field_simp` and
  `linarith`, gives `s = 75/2 cm = 37.5 cm`, which unfolds to answer A.
- The side and real/virtual hypotheses remain unused because the signed
  height, magnification laws, distance positivity, and calibration already
  contain all algebraic facts required by the conclusion.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0113.lean` exited 0.
- Lean LSP diagnostics report no errors and no `declaration uses sorry`
  warning. The only warnings are unused-variable linters on frozen physical
  context hypotheses.
- `lean_verify` for the fully qualified theorem reports only `propext`,
  `Classical.choice`, and `Quot.sound`; its source scan reports no suspicious
  patterns.
- A direct source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.

## Blueprint status

- No new declaration needs a blueprint entry.
- The existing target environment
  `thm:physics:phyx_mini_0113:target` is ready to be marked `\leanok` by the
  blueprint-marker sync. This prover lane did not edit the chapter because
  its explicit write permissions allow changes only to the assigned Lean file
  and this task-result report.

## Redraft needed

None.

## Why I stopped

Real progress: the file's sole sorry was closed honestly, the theorem compiles,
and axiom/source verification passed. There is no remaining proof obligation
in the assigned file.
