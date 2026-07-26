# Prover result: `problem_phyx_mini_0385.lean`

## Status

Complete. All five `sorry` placeholders were replaced with sound proofs, and
the assigned Lean file compiles.

## Declarations proved

- `bottomPressureIsHighestInWater`: uses the positive water density and
  gravitational acceleration to show that the hydrostatic term `ρ g d` is
  monotone in depth, so the full water depth at the cylinder bottom attains
  and dominates every admissible water pressure.
- `bottomPressureInPascals_sourceFormula`: specializes the layered
  hydrostatic laws to coherent SI units and chains the atmospheric, air,
  gasoline, and water pressure relations.
- `bottomPressureInKilopascals_eq`: substitutes the stated heights,
  atmospheric pressure, and explicit textbook calibration into the source
  formula and proves the exact value `453 / 4 kPa`.
- `highestPressureInWater_matches_choiceB_underCalibration`: combines the
  maximum and exact-value lemmas, then checks all four displayed values to
  prove that B is uniquely closest.
- `highestPressureInWater_fromSource`: combines the source-supported maximum
  and symbolic formula, with the numerical choice-B conclusion remaining
  conditional on the separately named calibration.

## Verification

- Lean LSP diagnostics report no errors and no `sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0385.lean` passed. Its only
  warnings are that the frozen `hScenario` and `hFigure` hypotheses are not
  needed by the law-based final proof.
- The Lean axiom check for
  `PhyXMiniProblems.ProblemPhyXMini0385.highestPressureInWater_fromSource`
  reports only the standard foundational dependencies `propext`,
  `Classical.choice`, and `Quot.sound`.
- Source scans found no `sorry`, `admit`, declared `axiom`, `sorryAx`, or
  `native_decide`.
- No declaration signature or hypothesis was changed.

## Blueprint synchronization

The four supporting declaration environments and the target theorem
environment are ready for `\leanok`. The blueprint was not edited because the
prover-stage write permissions allow changes only to the assigned Lean file
and this task-result file.

## Project metadata note

The requested run-local `.archon/AGENTS.md` is absent. The prover followed the
injected role instructions, `.archon/prover-modes/physics.md`,
`.archon/PROGRESS.md`, the complete physics blueprint chapter, the linked
source report, and the existing post-formalization audit. No
`/- USER: ... -/` comment was present in the assigned Lean file. The advertised
`archon dag-query` helper is also absent from `PATH`; no graph dependency was
needed for these local proofs.

## Redraft needed

None.
