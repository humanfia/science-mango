# Prover result: `problem_phyx_mini_0782.lean`

## Outcome

- Closed all three proof obligations without changing any declaration
  signature: `vertical_angular_speed_squared`,
  `vertical_angular_speed_exact`, and `problem_phyx_mini_0782`.
- No `sorry`, `admit`, new axiom, `sorryAx`, `native_decide`, or other proof
  escape hatch remains.
- No redraft is needed.

## Proof summary

- Specialized the governing inertia laws to kilograms and metres. The uniform
  bar contributes `76/375 kg m²`, the remaining endpoint ball contributes
  `2/5 kg m²`, and the total inertia is therefore `226/375 kg m²`.
- Specialized the energy laws to SI units. Release from rest makes the initial
  rotational kinetic energy zero, while the remaining ball's potential-energy
  drop is `49/5 J`. Energy conservation and
  `K = (1/2) I ω²` then give `ω² = 3675/113`.
- Used the actual `NNReal` nonnegativity of the dimensionful angular-speed
  readout and `Real.sqrt_sq` to select the positive root
  `ω = sqrt (3675/113)`.
- Certified the rational bounds
  `5.70 < sqrt (3675/113) < 5.71` by comparing squares. These bounds prove the
  requested `0.01 rad/s` tolerance and, by exhaustive case analysis over the
  four displayed choices, that B is uniquely closest.
- `hScenario`, `hPositive`, and `hFigure` are intentionally not needed after
  the readout and governing-law hypotheses determine the numerical result.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0782.lean` succeeds. Its
  only messages are unused-variable linter warnings for the frozen hypotheses
  `hScenario`, `hPositive`, and `hFigure`.
- `git diff --check` succeeds.
- A source scan finds no proof placeholder or suspicious proof mechanism.
- `lean_verify` for all three completed declarations reports no suspicious
  source patterns and only the standard axioms `propext`, `Classical.choice`,
  and `Quot.sound`.

## Blueprint readiness

The theorem and two lemma environments are ready for deterministic `\leanok`
synchronization. The blueprint was not edited because the prover write
permissions explicitly restrict changes to the assigned Lean file and this
task-result report.

## Environment note

The requested run-local `.archon/AGENTS.md` is absent. The available
`.archon/prover-modes/physics.md` and `.archon/PROGRESS.md` were used for the
prover role and project state.

## Redraft needed

None.
