# Autoformalization result: `problem_phyx_mini_0749.lean`

The chapter contains `% archon:physics`, so the physics-formalize discipline was used. The primary image `phyx_data/test_image/749.png`, source report, retry gate, prior grounding log, blueprint chapter, and assigned Lean file were inspected. The exact retry reason was that the physics target did not directly import Mathlib. This was resolved with `import Mathlib`, and the complete existing physical statement was audited and retained.

## Assumption/target split

### Governing laws

- The signed ground-frame sled velocity is the negative of the nonnegative plotted speed magnitude `v_s`.
- Galilean horizontal velocity addition relates the ball's ground-frame velocity, sled-frame launch component, and sled velocity.
- Uniform horizontal motion gives `Delta x_bg = v_bg,x * T` for every plotted sled speed.
- Uniform downward gravitational motion gives `Delta y = v0y * T - g * T^2 / 2`.
- The selected physical flight has positive duration and positive gravitational acceleration.

These appear only in `SatisfiesIdealSledProjectileLaws` and `HasPhysicalSledProjectileParameters`; neither predicate states a requested numerical result.

### Previous-part results

- The source report lists no previous parts.
- Consequently, no previous-part result is assumed.
- `graphDeterminesHorizontalLaunchVelocityAndFlightDuration` derives `v0x = 10 m/s` and `T = 4 s` as a lemma conclusion; those values are not premise fields of the final theorem.

### Figure/data and scenario readouts

- The left panel identifies the sled and ball, positive `x`/`y` axes, and a left-pointing `v_s` arrow.
- The right panel places `v_s` in metres per second on the horizontal axis and `Delta x_bg` in metres on the vertical axis.
- Primary-image graph points are `(0 m/s, 40 m)`, `(10 m/s, 0 m)`, and `(20 m/s, -40 m)`, with a straight displayed line and the printed ticks.
- The problem idealization says the ball lands at its launch height.
- The ideal near-Earth model uses `g = 9.80 m/s^2`.
- Answer labels A--D and their printed values are represented as dataset/display metadata. Recorded choice C is not a theorem premise.

### Current target conclusions

- `graphDeterminesHorizontalLaunchVelocityAndFlightDuration`: the graph and horizontal laws imply `v0x = 10 m/s` and `T = 4 s`.
- `verticalLaunchVelocityInMetersPerSecond_eq_19_6`: the graph, level endpoints, standard gravity, positivity, and kinematic laws imply `v0y = 19.6 m/s`.
- `problem_phyx_mini_0749`: the requested signed vertical sled-frame launch component is `19.6 m/s`, matches displayed choice C, and C is the unique closest printed choice.

## Goal-faithfulness audit

The independent field `SledProjectileSetup.launchVelocityRelativeToSledY` is not defined from an answer choice. No premise structure contains `v0y = 19.6`, choice C, the 4 s flight time, or the 10 m/s horizontal launch component. The only numerical premise data are the graph readouts, endpoint-height equality, and standard gravity. The ideal-motion predicate contains general kinematic equations, not their solved consequences.

The number `19.6` also occurs in `AnswerChoice.verticalSpeedMetersPerSecond` because it is literal multiple-choice metadata. `MatchesDisplayedVerticalSpeed` and `IsUniqueClosestVerticalSpeedChoice` occur only in conclusions, never as hypotheses, so unfolding them cannot supply the substantive vertical-velocity result. The main result remains dependent on the figure and governing-law premises.

The image supports the recorded answer: the graph slope is `-4 s`; its intercepts give `v0x = 10 m/s` and `T = 4 s`; level-flight vertical kinematics then gives `v0y = g*T/2 = 19.6 m/s`.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0749:target` corresponds to `problem_phyx_mini_0749`.
- Derived proof-route lemmas: `graphDeterminesHorizontalLaunchVelocityAndFlightDuration` and `verticalLaunchVelocityInMetersPerSecond_eq_19_6`.
- Dimension/readout helpers: `velocityDimension`, `accelerationDimension`, `SignedLengthQuantity`, `DurationQuantity`, `SignedVelocityQuantity`, `AccelerationMagnitudeQuantity`, `signedLengthInMeters`, `durationInSeconds`, `signedVelocityInMetersPerSecond`, `speedInMetersPerSecond`, `accelerationInMetersPerSecondSquared`, `speedFromMetersPerSecond`, `graphSledSpeedZero`, `graphSledSpeedTen`, and `graphSledSpeedTwenty`.
- Figure vocabulary and setup: `ArrowDirection`, `FigureObject`, `FigureQuantityLabel`, `GraphAxisQuantity`, `SledProjectileFigure`, and `SledProjectileSetup`.
- Premise interfaces: `MatchesPrimaryFigure`, `MatchesProblemDescription`, `UsesStandardNearEarthGravity`, `HasPhysicalSledProjectileParameters`, and `SatisfiesIdealSledProjectileLaws`.
- Display metadata/conclusion vocabulary: `AnswerChoice`, `AnswerChoice.verticalSpeedMetersPerSecond`, `recordedAnswerChoice`, `MatchesDisplayedVerticalSpeed`, and `IsUniqueClosestVerticalSpeedChoice`.

These public helper declarations do not have separate blueprint environments yet. The blueprint target environment should be marked `\leanok` and helper entries may be added after names stabilize; this agent did not edit the chapter because the task's final write-permissions section authorizes only the assigned Lean file and this report.

## LeanExplore queries and candidates actually used

All queries used `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical quantity SI units`: selected `Dimensionful`, `UnitChoices.SI`, and `CarriesDimension.toDimensionful`.
- `DimSpeed physical speed with dimensions`: selected `DimSpeed`. The short generated description said "Dimensionless Speed", but the fetched source confirms that it is the dimensionful type `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `WithDim Dimensionful CarriesDimension.toDimensionful`: selected `WithDim`, `Dimensionful`, and `CarriesDimension.toDimensionful`.
- `Dimension.L𝓭 Dimension.T𝓭 physical dimensions` and `Dimension.T𝓭`: selected `Dimension.L𝓭` and `Dimension.T𝓭`.
- `LengthUnit.meters TimeUnit.seconds`: `UnitChoices.SI` was the useful candidate; its fetched source explicitly chooses `LengthUnit.meters` and `TimeUnit.seconds`.
- `projectile motion under uniform gravity kinematics`: returned `RigidBodyMotion.velocity`, `RigidBodyMotion.displacement`, and related rigid-body declarations. They were not used because rigid-body pose kinematics does not state this projectile's Galilean frame addition and uniform-gravity equations.

Source and module data were fetched only for the candidates used in the file: `Dimensionful`, `WithDim`, `UnitChoices.SI`, `CarriesDimension.toDimensionful`, `DimSpeed`, `Dimension.L𝓭`, and `Dimension.T𝓭`.

## PhysLean/Mathlib names grounded

- `Dimensionful`, `UnitChoices.SI`, and `CarriesDimension.toDimensionful` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `DimSpeed` from `Physlib.Units.WithDim.Speed`.
- `Dimension.L𝓭` and `Dimension.T𝓭` from `Physlib.Units.Dimension`.
- `LengthUnit.meters` and `TimeUnit.seconds`, confirmed through the fetched implementation of `UnitChoices.SI`.
- Mathlib supplies `ℝ`, `NNReal`, ordered-real arithmetic, finite enumerations, and absolute value through the explicit `import Mathlib`. No specialized Mathlib physics theorem is claimed.

## Local abstractions introduced

- Signed length and signed velocity components use Physlib's `Dimensionful (WithDim d ℝ)`, while duration, speed, and acceleration magnitude use nonnegative carriers. Thus these are dimensional physical quantities, not transparent scalar aliases.
- `SledProjectileFigure` preserves literal objects, labels, directions, axes, ticks, and units from the image while keeping schematic coordinates separate from measurements.
- `SledProjectileSetup` distinguishes sled-frame launch components, ground-frame velocities, displacement, duration, gravity, and endpoint heights.
- The five premise structures separate primary-image evidence, prose scenario data, standard-gravity calibration, physical positivity, and governing kinematic laws.
- `AnswerChoice` preserves printed answer metadata without turning the recorded answer into an assumption.

## Grounding gaps

- LeanExplore found no directly matching Mathlib/Physlib theorem for ideal projectile motion with a moving launch frame, Galilean horizontal velocity addition, and the uniform-gravity displacement equation. `SatisfiesIdealSledProjectileLaws` is therefore a faithful local governing-law interface.
- No dedicated Physlib type for a signed one-dimensional velocity component was found. The composition `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)` preserves both sign and physical dimension.
- `archon dag-query` could not be run because `archon` was not on the process PATH, despite the runtime note. The source report has no previous parts and the target chapter declares no dependencies, so no dependency declaration was imported by guesswork.
- The requested `.archon/AGENTS.md` was absent on disk. The available `PROGRESS.md` and `.archon/prover-modes/physics-formalize.md` supplied the stage instructions.

## Verification

- `archon-lean-lsp` diagnostics: no errors or failed dependencies; exactly three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0749.lean`: exit code 0 with the same three expected warnings.

