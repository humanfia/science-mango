# Prover result: `problem_phyx_mini_0408.lean`

## Status

Complete. The sole proof obligation,
`heatDifferenceBetweenPaths_eq_initialPressure_mul_initialVolume`, is closed
without changing its signature.

## Proof summary

- Specialized the quasistatic boundary-work law to all four displayed legs.
- Used the figure's process classifications to show that the two vertical,
  isochoric legs do zero work.
- Rewrote the upper horizontal leg using pressure `2 p_i` and the volume
  change `2 V_i - V_i`, and rewrote the lower horizontal leg using pressure
  `p_i` and the same volume change.
- Specialized path-work additivity and the closed-system first law to paths
  `A` and `B`.
- Reduced the finite path/state definitions and used `nlinarith` to cancel the
  common endpoint internal-energy change and derive
  `Q_A - Q_B = p_i V_i`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0408.lean` succeeds.
- The root `lake build` succeeds with 4 jobs.
- Lean LSP diagnostics contain no errors.
- The theorem axiom audit reports only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`; its source scan reports no warnings.
- A source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide` in the assigned file.
- `git diff --check` reports no whitespace errors.

## Blueprint readiness

The target environment
`thm:physics:phyx_mini_0408:target` is ready for deterministic `\leanok`
synchronization. The blueprint was not edited because the task's final
write-permission block permits changes only to the assigned Lean file and this
task-result file.

## Environment notes

- The requested run-local `.archon/AGENTS.md` is absent, as already recorded
  in `.archon/PROGRESS.md`; the supplied prover instructions and
  `.archon/prover-modes/physics.md` were followed.
- The advertised `archon` executable was unavailable on `PATH`, so the
  optional dependency-graph query could not run. The target was proved using
  only its local figure and governing-law hypotheses.

## Redraft needed

None.
