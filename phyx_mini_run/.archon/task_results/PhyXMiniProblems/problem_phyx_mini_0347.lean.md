# Prover result: `problem_phyx_mini_0347.lean`

## Status

Complete. Both proof obligations are closed:

- `PhyXMiniProblems.ProblemPhyXMini0347.pressureAtA_from_adiabatic`
- `PhyXMiniProblems.ProblemPhyXMini0347.thermalEfficiency_choiceB`

The frozen declaration signatures and physical hypotheses were preserved. The
assigned file contains no remaining `sorry`, `admit`, axiom, `native_decide`,
or other proof escape.

## Proof summary

- The pressure theorem combines the supplied adiabatic pressure-volume ratio
  with the figure values for `Vₐ`, `Vᵦ`, `γ`, and the `1.5 atm` pressure at
  state `b`. Positivity of `pᵦ` and the figure pressure equation discharge the
  two nonzero denominators needed to convert the pressure ratio to
  atmospheres.
- The efficiency theorem eliminates the three state temperatures using the
  ideal-gas equations and `Cᵥ (γ - 1) = R`.
- The first law then gives explicit formulas for `W_ab` and `Q_ca`; the
  supplied isobaric and isochoric work laws give the remaining two work terms.
  After substituting the adiabatic pressure ratio, the exact efficiency is
  reduced to

  `(10 * r - 59) / (10 * (r - 1))`,

  where `r = Real.rpow (9 / 2) (7 / 5)`.
- The numerical comparison is rigorous rather than floating-point based.
  Raising `r` to the fifth power gives `(9 / 2)^7`, from which rational power
  comparisons prove

  `41 / 5 < r < 8213 / 1000`.

  These imply that the efficiency lies between `319 / 1000` and `321 / 1000`.
  Exhausting the four finite choices and simplifying the absolute values then
  proves that `319 / 1000` (choice B) is closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0347.lean` exits with code
  0 and no diagnostics.
- Source scan finds no `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`,
  or suspicious proof escape.
- `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`
  for both proved declarations, with no warnings.

## Blueprint

The theorem environments are ready for deterministic `\leanok`
synchronization. The blueprint chapter was not edited because the prover's
explicit write permissions restrict changes to the assigned Lean file and
this task-result file.

The requested run-local `.archon/AGENTS.md` is absent; the role instructions
in the assigned objective and `.archon/PROGRESS.md` were followed.

## Redraft needed

None. The statement is faithful to the supplied thermodynamic model and is
provable from its governing-law and figure-data hypotheses.
