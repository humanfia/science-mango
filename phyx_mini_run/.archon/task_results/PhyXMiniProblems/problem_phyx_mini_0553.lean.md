# `PhyXMiniProblems/problem_phyx_mini_0553.lean`

## Summary

- Closed both assigned placeholders without changing either declaration
  signature.
- Sorry count: 2 → 0.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0553.lean` exits with code
  0.
- The only diagnostic is the existing unused-variable linter warning for
  `hPhysical`, which is retained because the theorem signature is frozen.

## `missile_speed_fraction_measured_by_earth`

- **Result:** RESOLVED.
- Rewrote the governing Einstein velocity-addition relation using
  `hRelativity.missileVelocityTransformation`.
- Substituted the supplied fractions with
  `hData.spaceshipSpeedFraction` and `hData.missileLaunchSpeedFraction`.
- `norm_num` verifies
  `((4/5) + (3/5)) / (1 + (4/5)(3/5)) = 35/37`.

## `problem_phyx_mini_0553`

- **Result:** RESOLVED.
- Applied `missile_speed_fraction_measured_by_earth` for the exact
  Earth-frame speed fraction.
- Unfolded the matching and nearest-hundredth predicates for recorded choice D.
- Split over all four `AnswerChoice` constructors. Exact rational
  normalization proves D lies within `1/200` of `35/37`, rules out A, B, and C,
  and proves uniqueness.

## Faithfulness and safety

- The physical relation is used only through the stated
  `SatisfiesCollinearEinsteinVelocityAddition` hypothesis.
- The result distinguishes the exact speed `35/37 c` from the rounded displayed
  answer `0.95 c`.
- No axioms, `sorryAx`, `admit`, `native_decide`, metaprogramming, or signature
  changes were introduced.
- No redraft is needed.

## Blueprint status

- The proved declarations correspond to
  `lem:physics:phyx-mini-0553:phyxminiproblems-problemphyxmini0553-missile-speed-fraction-measured-by-earth`
  and `thm:physics:phyx_mini_0553:target`.
- Both environments are ready for `\leanok`. The blueprint was not edited
  because this prover's explicit write permissions allow only the assigned
  Lean file and this task-result file.

## Project instruction note

- `.archon/AGENTS.md` is absent in this workspace. Role instructions were read
  from `.archon/PROGRESS.md` and `.archon/prover-modes/physics.md`.
