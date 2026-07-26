# Prover result: `problem_phyx_mini_0357.lean`

## Status

Complete. Both proof obligations were closed without changing either
declaration signature:

- `exactNetWorkFromCircularDiagram`
- `netWorkDoneByGasInOneCycle`

No `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide` remains in the
assigned Lean file.

## Proof summary

- The circular-diagram geometry law, clockwise orientation, and unit coordinate
  radii give the oriented diagram area `Real.pi`.
- The pressure scale converts to `100000 Pa` per vertical unit and the volume
  scale converts to `1 / 1000 m³` per horizontal unit. The boundary-work law
  therefore gives the exact net work `100 * Real.pi J`.
- Mathlib's certified bounds `Real.pi_gt_d20` and `Real.pi_lt_d20` show that
  `100 * Real.pi` lies strictly within `1 / 2 J` of `314 J`, establishing the
  recorded answer choice A.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0357.lean` exits with code
  0. Its only diagnostics are unused-variable warnings for the frozen
  `h_physical` and `h_cycle` hypotheses.
- Root `lake build` completes successfully (4 jobs).
- Source scan finds no proof placeholders or escape hatches.
- `lean_verify` reports no suspicious source patterns for either proved
  declaration. Each uses only the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `git diff --check` reports no whitespace errors.

## Blueprint status

Both proof environments are ready for `\leanok` synchronization. The blueprint
was not edited because the explicit prover permissions restrict writes to the
assigned Lean file and this task-result file.

The requested run-local `.archon/AGENTS.md` is absent, as also recorded in
`.archon/PROGRESS.md`; the supplied role instructions and
`.archon/prover-modes/physics.md` were followed.

## Redraft needed

None.
