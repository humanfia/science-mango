# PhyXMiniProblems/problem_phyx_mini_0369.lean

## Result

- `isothermTemperature_exact_kelvins` and
  `isothermTemperature_matches_recordedAnswerA` are fully proved.
- The exact proof transfers the state-1 figure readouts to the physical gas
  state, converts `100 kPa` to `100000 Pa`, identifies the state temperature
  with the curved isothermal process temperature, and applies
  `pV = nRT` with `V = 2 m³`, `n = 80 mol`, and
  `R = 8.31 J mol⁻¹ K⁻¹`.
- This yields `T = 250000 / 831 K`; exact rational inequalities then prove
  that the value rounds to `301 K`, recorded answer A.
- No `sorry`, `admit`, `axiom`, `native_decide`, or `sorryAx` occurs in the
  assigned Lean file.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0369.lean` completed with
  exit code 0 and no diagnostics.
- Lean LSP diagnostics are empty.
- Axiom/source verification for both proved declarations reports no
  suspicious source patterns and only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`.
- `git diff --check` reports no whitespace errors.

## Blueprint status

Both proof declarations are closed and ready for the authorized
`sync_leanok` phase. The blueprint was not edited because the prover is
explicitly restricted to the assigned Lean file and this task-result file.

## Workflow note

The requested run-local `.archon/AGENTS.md` is absent, as
`.archon/PROGRESS.md` also records. The available run-local
`.archon/prover-modes/physics.md` instructions were followed.

## Redraft needed

None.
