# Prover result: `problem_phyx_mini_0960.lean`

## Outcome

Closed both proof obligations without changing either declaration signature:

- `totalMagneticFieldAtP_exact`
- `problem_phyx_mini_0960`

The exact-field proof derives the SI readouts
`d = 3/2000 m`, `r = 2/25 m`, and wire separation `1/20 m` from
the written data, and the currents `12 A` and `24 A` from the calibrated
primary figure.  The geometry hypotheses reduce both current-direction cross
products to `(-5/16) • zHat`.  Substitution into the supplied short-segment
Biot--Savart law gives the two into-page contributions
`45/512000000 T` and `90/512000000 T`; superposition therefore gives the
target `135/512000000 T`.

The final theorem uses the supplied norm relation and the unit norm of the
page-normal vector to obtain the exact magnitude.  Direct rational arithmetic
then proves the nearest-nanotesla rounding to answer B and checks B is strictly
closer than A, C, or D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0960.lean`: exit code 0.
- `lake build`: completed successfully.
- The generated file is outside the declared `PhyxMiniRun` library, so Lake
  has no separate `PhyXMiniProblems.problem_phyx_mini_0960` build target; the
  file-level Lean invocation is the definitive module check.
- Source scan found no `sorry`, `admit`, added `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification of
  `PhyXMiniProblems.ProblemPhyXMini0960.problem_phyx_mini_0960` reports only
  Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.
- The compiler emitted only non-fatal lints: the frozen lemma arguments
  `hPhysical` and `hSteady` are not needed by the calculation, and
  `EuclideanSpace.norm_single` is deprecated in favor of `PiLp.norm_single`.

## Blueprint status

The lemma and theorem proof environments are ready for deterministic
`\leanok` synchronization.  The blueprint was not edited because the prover
role permits writes only to the assigned Lean file and this task-result file.

## Redraft needed

None.

## Infrastructure note

The run-local `.archon/AGENTS.md` was absent, as documented in
`.archon/PROGRESS.md`; the identical canonical archive copy was read instead.
