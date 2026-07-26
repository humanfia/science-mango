# Autoformalization result: `problem_phyx_mini_0396.lean`

## Assumption/target split

### Governing laws

- `SatisfiesCylinderAndPistonKinematics.circularPistonArea`: the cylinder/piston area is `π(d/2)²`.
- `SatisfiesCylinderAndPistonKinematics.compressionMeasuredFromBottom`: the unloaded-at-bottom spring reference makes piston height above the bottom equal spring compression.
- `SatisfiesCylinderAndPistonKinematics.cylindricalGasVolume`: `V = A h` for each gas state.
- `SatisfiesCylinderAndPistonKinematics.finalHeightAfterRise`: the final piston height is the initial height plus the stated rise.
- `SatisfiesLinearSpringAndStaticEquilibrium.hookeLaw`: `F_s = k x` in coherent SI readouts.
- `SatisfiesLinearSpringAndStaticEquilibrium.quasistaticVerticalForceBalance`: `P_gas A = P_atm A + m g + F_s` in each state.
- `UsesTextbookTerrestrialGravity.gravityInSI`: the numerical calculation uses the standard textbook calibration `g = 9.8 m/s²`.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- Piston mass `5 kg`, circular-cylinder diameter `100 mm`, external atmospheric pressure `100 kPa`, shown-state pressure `400 kPa`, shown-state gas volume `0.4 L`, and piston rise `2 cm`.
- The spring is linear and exerts zero force at the cylinder bottom.
- The valve is opened so that air flows from the supply line into the cylinder.
- The gas state shown in the image uses the shown piston position; the post-admission state uses the raised position.
- Image `396.png` shows the vertical cylinder, top-mounted spring attached to the piston, air below the piston, `P₀` above it, downward `g`, and an air-supply line with an in-line valve connected to the gas region.

### Current target conclusions

- The final pressure is within `0.1 kPa` of the displayed `515.3 kPa` value.
- At that tolerance, B is the unique matching displayed choice.

## Goal-faithfulness audit

The final pressure is an independent field of `SpringLoadedPistonSetup`. No premise structure states its numerical value, bounds it near `515.3 kPa`, selects answer B, or defines it from an answer choice. The force-balance premise mentions the final pressure only through the same state-uniform physical law imposed on both states. The spring stiffness is also independent and must be calibrated from the shown-state equilibrium, initial volume/height, and unloaded-at-bottom condition. `answerPressureInKilopascals` only transcribes all four printed choices; the theorem itself must derive that the independent final pressure is close to B and far from every competing choice.

The `0.1 kPa` tolerance expresses agreement with the finite precision of the recorded multiple-choice value. With exact `Real.pi` and the standard `9.8 m/s²` gravity calibration, the model predicts approximately `515.36 kPa`; hence an exact equality to the one-decimal display would be an artificial strengthening.

## Declarations and blueprint labels

- `SpringLoadedPistonSetup`: independent physical quantities and apparatus roles.
- `SpringLoadedPistonFigure`: primary-image geometry, components, and label targets.
- `MatchesProblemAndPrimaryFigure`: prose and image readouts.
- `UsesTextbookTerrestrialGravity`: gravitational calibration.
- `HasPhysicalParameters`: physical positivity conditions.
- `SatisfiesCylinderAndPistonKinematics`: circular-cylinder geometry and the piston/spring reference kinematics.
- `SatisfiesLinearSpringAndStaticEquilibrium`: Hooke and quasistatic force-balance laws.
- `newPressure_matches_recordedAnswerB`: corresponds to `thm:physics:phyx_mini_0396:target`.

## LeanExplore queries and candidates used

- Query: `physical dimensionful pressure force mass length area spring stiffness Hooke law`, packages `Mathlib`, `Physlib`.
  - Used candidates: `DimArea`, `DimPressure`, `Dimension`, and the dimension notation `Dimension.L𝓭`.
  - Near matches not used: `ClassicalMechanics.DampedHarmonicOscillator.force` and Newton's-second-law examples do not model a pressure-loaded quasistatic piston.
- Query: `DimPressure Dimensionful WithDim DimForce`, packages `Mathlib`, `Physlib`.
  - Used candidates: `Dimensionful` and `DimPressure`. `DimPressure.pascal` was inspected as confirmation of the SI pressure representation but is not referenced directly. There was no `DimForce` candidate.
- Query: `DimMass DimLength DimForce`, packages `Mathlib`, `Physlib`.
  - Used the returned dimension infrastructure rather than inventing unavailable names.
- Query: `spring constant stiffness physical dimension force per length`, packages `Mathlib`, `Physlib`.
  - The harmonic-oscillator results were near misses; the local dimension-tagged spring stiffness and explicit Hooke predicate better preserve this apparatus's role.

Fetched LeanExplore source/module data for `DimArea` (`Physlib.Units.WithDim.Area`), `DimPressure` and `DimPressure.pascal` (`Physlib.Units.WithDim.Pressure`), and `Dimensionful` (`Physlib.Units.Basic`).

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `DimArea`, `DimPressure`, and `UnitChoices.SI`.
- Mathlib: `Real.pi` and real absolute value `abs`.

## Local abstractions introduced

- Dimension-tagged `MassQuantity`, `LengthQuantity`, `VolumeQuantity`, `AccelerationQuantity`, `ForceQuantity`, and `SpringStiffnessQuantity` fill gaps where no matching Physlib ready-made type was found. They are not scalar aliases: each is a unit-independent `Dimensionful (WithDim ... ℝ)` carrying its physical dimension.
- `GasState`, `PistonPosition`, and the figure enumerations preserve the state distinctions, the unloaded bottom reference, directions, component connections, and image labels.
- The physical laws are explicit propositions over coherent SI readouts; this avoids hiding the requested pressure in a local definition.

## Grounding gaps and redraft requests

- LeanExplore exposed no ready-made dimensionful quasistatic spring-loaded-piston or Hooke/pressure force-balance API compatible with this problem. The file therefore states those laws locally and explicitly.
- The requested `.archon/AGENTS.md` and assigned Lean file were absent at task start. The available `.archon/prover-modes/physics-formalize.md` supplied the applicable role instructions, and the Lean file was created with a `USER` comment recording its initial absence.
- The `archon` executable was not available on `PATH`, so the optional dependency-graph queries could not be run.
- The blueprint chapter was not edited because this task's explicit write permissions allow edits only to the assigned Lean file and this task-result file. The orchestrator should add `\leanok` to `thm:physics:phyx_mini_0396:target` after accepting the declaration.
