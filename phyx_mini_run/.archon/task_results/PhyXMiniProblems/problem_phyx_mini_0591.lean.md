# Autoformalization result: `problem_phyx_mini_0591.lean`

## Assumption/target split

### Governing laws

- `ObeysCollinearLorentzVelocityTransformation` states the general signed,
  one-dimensional Lorentz transformation from the Earth frame to the
  south-entry particle's rest frame:
  `beta_(N|S) = (beta_(N|E) - beta_(S|E)) /
  (1 - beta_(S|E) * beta_(N|E))`.
- `RelativeApproachSpeedIsMagnitude` states the operational relation between
  the requested nonnegative speed and the magnitude of that transformed
  signed velocity.
- `HasPhysicalCosmicRayParameters` supplies positivity of the selected
  readout of `c`, signs of the two Earth-frame velocities, and subluminality.
  It constrains the unknown relative speed only by positivity and
  subluminality.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesPrimaryFigure` records that the bitmap shows Earth, the common
  north--south axis, the axial rotation marker, the north and south pole
  labels and order, the two pole-entry assignments, the two inward arrow
  directions, and speed magnitudes `4/5 c` and `3/5 c`.
- `MatchesEarthFrameVelocityReadouts` chooses northward as positive and records
  the signed Earth-frame values `-4/5 c` and `+3/5 c`, together with the Earth
  and south-entry-particle frame labels.

### Current target conclusions

- The north-entry particle has exact signed velocity `(-35/37)c` in the
  south-entry particle's rest frame.
- The relative approach speed is exactly `(35/37)c`.
- This exact value rounds to the displayed `0.95c`, and choice `C` is the
  unique matching displayed answer.

## Goal-faithfulness audit

The unknown transformed velocity and nonnegative relative speed are stored as
independent fields of `CosmicRayApproachSetup`. No setup field defines either
quantity from a solved expression or answer choice. The figure and readout
premises mention only the supplied `0.80c` and `0.60c` data. The governing-law
premise contains the unspecialized Lorentz velocity-transformation formula,
not `-35/37`, `35/37`, `0.95`, or choice `C`. The magnitude premise supplies
only the operational meaning of relative speed. The exact fractions and
unique answer choice occur only in the helper lemma and main theorem
conclusions.

The displayed decimal is modeled by `RoundsToNearestHundredth`; it is not
asserted as an incorrect exact equality to `35/37`. The drawn rotation marker
is retained as figure evidence but is not used to manufacture the target.

## Declarations created and blueprint correspondence

- Physical quantities/readouts: `SignedAxialVelocity`, `SpeedQuantity`,
  `signedVelocityReadout`, `speedReadout`,
  `vacuumSpeedOfLightReadout`, `velocityInLightSpeedUnits`, and
  `speedInLightSpeedUnits`.
- Labels and model: `ReferenceFrameLabel`, `GeographicPole`,
  `CosmicRayParticle`, `AxialDirection`, `CosmicRayAxisFigure`, and
  `CosmicRayApproachSetup`.
- Assumptions: `MatchesPrimaryFigure`,
  `MatchesEarthFrameVelocityReadouts`, `HasPhysicalCosmicRayParameters`,
  `ObeysCollinearLorentzVelocityTransformation`, and
  `RelativeApproachSpeedIsMagnitude`.
- Answer modeling: `AnswerChoice`, `displayedSpeedInLightSpeedUnits`,
  `recordedDatasetAnswer`, `RoundsToNearestHundredth`,
  `MatchesAnswerChoice`, and `IsUniqueMatchingAnswerChoice`.
- Derived declarations:
  `northEntryVelocityInSouthEntryFrame_exact` is an unlabeled helper lemma;
  `problem_phyx_mini_0591` formalizes
  `thm:physics:phyx_mini_0591:target`.

## LeanExplore grounding

Search-summary queries were run with `packages: ["Mathlib", "Physlib"]`:

- `special relativistic velocity addition relative velocity collinear particles`
- `velocity physical quantity with dimensions units speed`
- `speed of light`
- `Lorentz velocity transformation`
- `SpaceTime velocity`

Sources/modules/docstrings were inspected for these candidates:

- `DimSpeed` (`Physlib.Units.WithDim.Speed`) — used as the physical
  nonnegative speed type.
- `DimSpeed.speedOfLight` (`Physlib.Units.WithDim.Speed`) — used as the exact
  dimensionful vacuum speed of light.
- `Lorentz.Velocity` (`Physlib.Relativity.Tensors.RealTensor.Velocity.Basic`)
  — not used because it is a future-directed unit Minkowski four-velocity,
  whereas the source supplies ordinary signed coordinate-speed readouts.
- `SpeedOfLight` (`Physlib.Relativity.SpeedOfLight`) — inspected but not used;
  `DimSpeed.speedOfLight` integrates directly with the dimensionful speed API.
- `LorentzGroup.generalizedBoost`
  (`Physlib.Relativity.LorentzGroup.Boosts.Generalized`) — inspected but not
  used because it maps four-velocities and does not directly expose the
  one-dimensional coordinate-velocity readout required here.

## Physlib/Mathlib names grounded

The file uses `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
`DimSpeed`, `DimSpeed.speedOfLight`, `LengthUnit`, `TimeUnit`, and
`UnitChoices.SI` from `Physlib.Units.WithDim.Speed` and its imports. Signed
velocities therefore retain length-per-time dimension, and real numbers are
used only for readouts and dimensionless ratios.

## Local abstractions introduced

- `SignedAxialVelocity` is not a scalar alias: it is Physlib's unit-independent
  dimensionful length-per-time quantity over `ℝ`.
- The frame, pole, particle, and direction inductives preserve the physical
  roles and primary-image labels without treating drawing coordinates as
  physical distances.
- `CosmicRayAxisFigure` separates bitmap evidence from physical quantities;
  `CosmicRayApproachSetup` keeps the requested observables independent.
- The two governing-law structures provide the missing ordinary-coordinate
  velocity transformation and speed-magnitude interface without assuming the
  problem-specific result.

## Grounding gaps and redraft requests

- LeanExplore did not return a ready-made Physlib declaration for the
  one-dimensional Einstein transformation of ordinary signed coordinate
  velocities. The local governing-law structure states that standard law
  explicitly while using Physlib's dimensionful quantities for its inputs.
- The requested `.archon/AGENTS.md` is absent in this project state; the
  available `.archon/prover-modes/physics-formalize.md` and the full role text
  in the task prompt were followed instead.
- The `archon` executable was not available on `PATH`, so read-only DAG queries
  could not run. The blueprint contains no declared dependency environments,
  and the source report lists no previous parts.
- The blueprint chapter exists, but it was not edited to add `\leanok` because
  the task's explicit write permissions allow changes only to the assigned
  Lean file and this result file. A coordinator with blueprint write authority
  should add `\leanok` to the target environment.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0591.lean` exits successfully
with exactly the two expected `declaration uses sorry` warnings (the helper
lemma and main theorem) and no errors.

---

# Prover result — iteration 017

## Outcome

All `sorry` placeholders in
`PhyXMiniProblems/problem_phyx_mini_0591.lean` were closed without changing
any declaration signature.

- `northEntryVelocityInSouthEntryFrame_exact`: rewrites the Lorentz
  transformation with the two Earth-frame readouts and proves the exact
  value `-35/37` by normalized rational arithmetic.
- `problem_phyx_mini_0591`: derives the speed `35/37` from the magnitude law,
  proves that it lies in choice C's nearest-hundredth interval, and checks by
  cases that choices A, B, and D cannot match.

No redraft is needed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0591.lean`: exit code 0.
- The only diagnostics are unused-variable linter warnings for the frozen
  `hFigure` and `hPhysical` premises.
- Source scan finds no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom audits of both completed declarations report only Lean/Mathlib's
  standard `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint status

The target and helper declarations are proof-complete. The blueprint was not
edited because this prover objective explicitly permits writes only to the
assigned Lean file and this task-result file. A blueprint-authorized
coordinator should add `\leanok` to the target theorem and helper lemma
environments.
