# Task result: `problem_phyx_mini_0909.lean`

## Status

Partial, with one frozen-statement blocker.

- `deflection_angle_eq_arctangent_prediction` is fully proved.
- The target theorem `problem_phyx_mini_0909` is fully proved, including the
  arctangent bounds and uniqueness of displayed choice C.
- In `exit_velocity_components`, the force and acceleration equations, the
  general horizontal update, and the entire vertical conjunct are proved.
- The only remaining `sorry` is focused on the missing proposition
  `electricFieldVectorInNewtonsPerCoulomb setup.electricField xAxis = 0`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0909.lean` exits with code
  0. Its only diagnostic is the expected warning that
  `exit_velocity_components` uses `sorry`.
- Lean LSP diagnostics likewise report no errors and exactly that one warning.
- The proof state at the remaining gap confirms that all available hypotheses
  yield only
  `v_exit,x = v_entry,x + q * E_x * t / m`.
- Axiom verification for the fully proved target theorem reports only
  `propext`, `Classical.choice`, and `Quot.sound`; it does not depend on the
  incomplete helper lemma.
- Source scanning found no `axiom`, `admit`, `native_decide`, or `sorryAx`
  laundering.

## Redraft needed

- Original problem: `phyx_mini_0909` (source id 909).
- Source report: `reports/phyx_mini/problem_phyx_mini_0909.source.json`.
- Theorem name:
  `PhyXMiniProblems.ProblemPhyXMini0909.exit_velocity_components`.
- Why the current statement is not provable: its hypotheses contain only
  positivity/nondegeneracy and the general uniform-field dynamics. Those laws
  imply
  `v_exit,x = v_entry,x + q * E_x * t / m`, not
  `v_exit,x = v_entry,x`. The physical assumptions make `q`, `t`, and `m`
  nonzero, while nothing requires `E_x = 0`; a nonzero horizontal field
  therefore gives a counterexample to the first conjunct.
- Smallest faithful statement change: add
  `electricFieldVectorInNewtonsPerCoulomb setup.electricField xAxis = 0` as a
  premise. Equivalently, add
  `_readouts : MatchesGivenElectronDeflectionReadouts setup`, whose
  `electricFieldHasNoHorizontalComponent` field is exactly the missing fact.

## Project notes

- The requested `.archon/AGENTS.md` is absent in this run. The current
  `.archon/PROGRESS.md` says the identical canonical archive supplies the
  active instructions, and `.archon/prover-modes/physics.md` was followed.
- The blueprint already exists and was read. It was not edited because this
  task restricts writes to the assigned Lean file and task-result file.
