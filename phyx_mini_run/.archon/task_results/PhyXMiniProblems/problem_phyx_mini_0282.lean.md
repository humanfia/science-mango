# Prover result: `problem_phyx_mini_0282.lean`

## Status

Complete. The sole `sorry` in
`PhyXMiniProblems.ProblemPhyXMini0282.pivotSeparation_is_answer_D` was replaced
by a sound proof without changing the declaration header.

## Proof

- Equal measured periods and Physlib's `period = 2π / ω` give equal angular
  frequencies at pivots A and B.
- Physlib's `ω² = k / m`, together with the two parallel-axis and gravitational
  restoring laws, gives the equality of the two physical-pendulum frequency
  ratios.
- Cancelling the positive mass and gravity factors and using the strict
  inequality between the two center-of-mass offsets yields
  `I_com = M * a * b`.
- Substitution gives `ω² * (a + b) = g`; the figure law `L = a + b` and the
  period law then give `L = g T² / (4π²)`.
- `Real.pi_gt_d6` and `Real.pi_lt_d6` certify that the resulting length is
  within `1/2000 m` of `0.804 m`. Exhausting the four displayed choices proves
  that D is uniquely closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0282.lean` succeeded.
- `lake build` succeeded.
- Source scan found no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Notes

- `.archon/AGENTS.md` is absent in this checkout; the explicit prover prompt
  and `.archon/PROGRESS.md` were followed.
- The blueprint chapter was read but not edited because this task grants write
  permission only for the assigned Lean file and this result file. An
  authorized orchestration step should add `\leanok`.
- No redraft is needed.
