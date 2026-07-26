# Prover result — Archon iteration 014

## Outcome

- Proved
  `PhyXMiniProblems.ProblemPhyXMini0146.emergenceAngleIsChoiceC`.
- Preserved the theorem signature, all physical hypotheses, and every supporting
  declaration.
- No redraft is needed.

## Proof summary

- The entry-face Snell equation and the exact `45°` sine value give
  `sin r = 25 * sqrt 2 / 77` for the internal refraction angle.
- The acute physical branch and `cos² r + sin² r = 1` then fix
  `cos r = sqrt 4679 / 77`.
- Equilateral-prism geometry gives the exit incidence angle as `60° - r`.
  Substitution in the exit-face Snell equation yields the exact relation
  `sin e = sqrt 14037 / 100 - sqrt 2 / 4`.
- Certified rational bounds on the square roots, together with the exact
  half-angle value for `sin (5π/16)`, place the emergence-angle readout
  strictly between `56.15°` and `56.25°`. A repeated half-angle estimate
  supplies the strict lower-margin comparison without adding imports.
- That interval proves the nearest-tenth predicate for `56.2°`; exhaustive
  case analysis on the four constructors proves choice C is uniquely nearest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0146.lean` succeeds.
- The assigned source contains no `sorry`, `admit`, introduced `axiom`,
  `native_decide`, or `sorryAx`.
- `lean_verify` reports no suspicious source patterns. The theorem depends
  only on the standard imported axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- The assigned file contains no `/- USER: ... -/` hint.

## Project metadata

- The requested `.archon/AGENTS.md` is absent in this checkout, as recorded in
  `.archon/PROGRESS.md`; the available `.archon/prover-modes/physics.md`,
  progress file, blueprint chapter, source report, and references summary were
  read and followed.
- The target blueprint environment is ready for `\leanok`. The blueprint was
  not edited because prover write permissions restrict changes to the assigned
  Lean file and this task-result file.

## Redraft needed

None.
