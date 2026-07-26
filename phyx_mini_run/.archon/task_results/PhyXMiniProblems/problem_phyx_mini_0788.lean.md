# Prover result: `problem_phyx_mini_0788.lean`

## Status

Complete. All five proof obligations are closed:

- `cliffEdge_speed_squared_from_rolling_energy`
- `cliffEdge_speed_squared_eq_233`
- `landing_speed_squared_from_initial_data`
- `landing_speed_squared_eq_3909_over_5`
- `landing_speed_selects_choice_B`

The frozen declaration signatures were preserved. No `sorry`, `admit`, custom
axiom, `native_decide`, or other proof escape hatch remains in the assigned
file.

## Proof summary

- The diagonal inertia entry needed for the fixed spin axis is proved locally
  from `RigidBody.solidSphere` and `RigidBody.inertiaTensor`; the proof does not
  use Physlib's `[sorryful]` theorem `RigidBody.solidSphere_inertiaTensor`.
- A cyclic coordinate linear isometry preserves the three-dimensional closed
  ball and its Haar measure, so the three coordinate-square integrals are
  equal. The radial Haar-integral formula gives
  `∫ ‖x‖² = (3/5) volume(ball) R²`; consequently each coordinate contributes
  `(1/5) volume(ball) R²`, and the required diagonal inertia is
  `(2/5) m R²`.
- The fixed-axis spin hypothesis then reduces rotational kinetic energy to
  `m r² ω² / 5`. The two no-slip laws give rotational energy `m v² / 5` at
  the initial and cliff-edge stages.
- Expanding conserved total energy at those stages, substituting the figure
  heights, and cancelling the positive mass yields
  `v_edge² = v_initial² - (10/7) g h`.
- The figure readouts `v_initial = 25`, `h = 28`, and `g = 9.8` specialize this
  to `v_edge² = 233`.
- Combining the edge relation with the horizontal-projectile drop law gives
  `v_landing² = v_initial² + (4/7) g h`, hence the exact value
  `v_landing² = 3909/5`.
- Nonnegativity of the dimensionful speed selects the positive square-root
  branch. Polynomial bounds prove `|v_landing - 28| < 1/20`; case analysis on
  the four displayed values proves that only choice B satisfies the same
  nearest-tenth predicate.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0788.lean` exits with code
  0 and no diagnostics.
- A source scan finds no `sorry`, `admit`, `axiom`, `native_decide`,
  `sorryAx`, or reference to `RigidBody.solidSphere_inertiaTensor`.
- `lean_verify` on
  `cliffEdge_speed_squared_from_rolling_energy`,
  `landing_speed_squared_eq_3909_over_5`, and
  `landing_speed_selects_choice_B` reports only the standard foundational
  axioms `propext`, `Classical.choice`, and `Quot.sound`, with no warnings.

## Blueprint synchronization

The five corresponding lemma/theorem proof environments are ready for
deterministic `\leanok` synchronization. The blueprint chapter was not edited
because the task's explicit write scope authorizes only the assigned Lean file
and this task-result file.

The requested run-local `.archon/AGENTS.md` is absent, as also recorded in
`.archon/PROGRESS.md`; the supplied prover instructions, physics prover-mode
document, blueprint chapter, and source report were used instead.

## Redraft needed

None.
