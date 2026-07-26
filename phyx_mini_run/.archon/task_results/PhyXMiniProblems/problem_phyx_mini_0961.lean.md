# Prover result: `problem_phyx_mini_0961.lean`

## Outcome

Closed both proof obligations without changing either declaration signature:

- `totalFieldMagnitudeAtP_exact`
- `magneticFieldMagnitudeAtMidpoint`

The exact-field proof derives the midpoint displacements
`(3/200) eₓ + (3/200) eᵧ` and
`(-3/200) eₓ + (-3/200) eᵧ`, in metres, from the primary-figure
geometry.  The two `2 mm` current elements reduce to `(1/500) eᵧ` and
`(1/500) eₓ`.  Both right-handed cross products are
`(-3/100000) e_z`, so the two Biot--Savart contributions point in the
same page-normal direction.  Their common displacement norm is
`3 * sqrt 2 / 200`, and substitution of the standard vacuum
permeability and `28 A` current gives the exact total magnitude
`14 * sqrt 2 / 1125000 T`.

The final theorem proves
`1.41421 < sqrt 2 < 1.41422` by squaring.  These bounds establish the
specified rounding interval for `1.76 × 10⁻⁵ T` and prove that answer B
is strictly closer than A, C, or D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0961.lean`: exit
  code 0.
- The file also compiles with `-DmaxHeartbeats=100000`.
- Source scan found no `sorry`, `admit`, added `axiom`, `native_decide`,
  or `sorryAx`-style escape hatch.
- Axiom verification of both completed declarations reports only
  Lean/Mathlib's standard `propext`, `Classical.choice`, and
  `Quot.sound`.
- The compiler emitted only non-fatal lints: the frozen exact-lemma
  arguments `hPhysical` and `hSteady` are not needed by the calculation,
  plus two unnecessary sequence-focus style warnings.

## Blueprint status

The lemma and theorem proof environments are ready for deterministic
`\leanok` synchronization.  The blueprint was not edited because prover
permissions restrict writes to the assigned Lean file and this task-result
file.

## Redraft needed

None.

## Infrastructure note

The requested run-local `.archon/AGENTS.md` is absent.  The available
`.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, blueprint chapter,
source report `reports/phyx_mini/problem_phyx_mini_0961.source.json`, and
file-specific `USER` comment were read.
