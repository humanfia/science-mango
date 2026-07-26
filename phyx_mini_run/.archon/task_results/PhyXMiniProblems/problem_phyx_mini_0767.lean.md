# Prover result: `problem_phyx_mini_0767.lean`

## Status

Complete. All three proof obligations are closed without `sorry`, `admit`,
new axioms, or proof escape hatches. Declaration signatures were unchanged.

## Proof summary

- `rim_impact_velocity_squared` specializes frictionless descent energy
  conservation, substitutes the release and height data, transports positive
  mass from SI to the arbitrary coherent unit choice, and cancels that mass to
  derive `v_impact² = 2 g R`.
- `common_velocity_after_sticking_is_half` uses the bottom body's zero incoming
  velocity, equal masses, and tangential momentum conservation. After the same
  unit-independent positive-mass argument, cancellation gives
  `v_after = v_impact / 2`.
- `problem_phyx_mini_0767` specializes the compound-body ascent energy law at
  the turning point, cancels the positive total mass, combines the two route
  lemmas, and transports positive gravitational acceleration from SI to the
  arbitrary unit choice. Cancelling gravity yields `h = R / 4`; unfolding the
  choice definitions proves that recorded choice B is correct.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0767.lean` succeeds with
  exit code 0. Its only diagnostics are unused-variable linter warnings for
  the qualitative `hScenario` and `hFigure` hypotheses.
- `lean_verify` reports only the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- A source audit finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.

## Blueprint readiness

The three proved declarations are ready for deterministic `\leanok`
synchronization. The blueprint was not edited because the prover-mode write
permissions restrict this task to the assigned Lean file and this result file.

## Dispatch note

`.archon/AGENTS.md` was absent in this checkout. The task was completed under
the checked-in `.archon/prover-modes/physics.md` instructions and the prover
objective supplied by the dispatcher.

## Redraft needed

None.
