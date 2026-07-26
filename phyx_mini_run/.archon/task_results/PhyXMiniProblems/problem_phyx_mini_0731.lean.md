# Autoformalization result: `problem_phyx_mini_0731.lean`

## Assumption/target split

### Governing laws

- `SatisfiesHorizontalFlightAndSlopeLaws.horizontalMotion`: horizontal distance from the slope foot is speed times elapsed time, in coherent SI readouts.
- `SatisfiesHorizontalFlightAndSlopeLaws.aircraftKeepsConstantElevation`: retaining the horizontal heading keeps the airplane at its initial elevation `h`.
- `SatisfiesHorizontalFlightAndSlopeLaws.upwardPlanarGround`: after horizontal distance `x`, the planar ground elevation is `x * tan(theta)`.
- `HasPhysicalFlightParameters` supplies positive speed, positive clearance, and the acute branch `0 < theta < pi/2`; it supplies no impact time.

### Previous-part results

- None. The source report has no previous parts.

### Figure/data readouts

- The physical speed has readout `1300 km/h`.
- The physical initial clearance labeled `h` has readout `35 m`.
- The slope angle labeled `theta` is `4.3 degrees = 43/10 degrees`.
- The slope begins at elapsed time zero.
- `GroundProfileKind`, `FlightHeading`, and `FlightDirection` retain the initially-level-then-upward-planar ground, unchanged horizontal heading, and motion into the rising slope.
- `RisingGroundFigure` records the airplane, level and sloping ground segments, horizontal dashed flight line, vertical clearance marker, and the physical `h` and `theta` labels visible in image 731.
- Direct inspection of `phyx_data/test_image/731.png` confirms level ground on the aircraft side, an upward planar segment in the intended travel direction, the `h` and `theta` labels, and no pictured impact-time value.

### Current target conclusions

- Existence of a positive first impact time at which aircraft and ground elevations coincide and before which the aircraft remains strictly above the ground.
- The exact relation
  `t = h / (v * Real.Angle.tan theta)` in metres, seconds, and metres per second.
- Agreement of that physical time with displayed answer C (`1.3 s`) to the half-tenth-second rounding tolerance.

## Goal-faithfulness audit

No impact duration is a field of `RisingGroundFlightSetup`. Neither `MatchesProblemAndFigure`, `HasPhysicalFlightParameters`, nor `SatisfiesHorizontalFlightAndSlopeLaws` mentions an impact time, the formula for it, a numerical collision-time readout, or an answer choice. `IsFirstGroundImpact` is used only on the conclusion side and gives the substantive collision/first-contact conditions. `MatchesAnswerChoice` is also conclusion-side; it does not define a physical duration to equal `1.3 s`. The only unfolding helpers are unit readouts, degree conversion, and the table of printed answer values.

## Declarations and blueprint labels

- Blueprint target `thm:physics:phyx_mini_0731:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0731.firstGroundImpact_matches_recordedAnswerC`.
- Dimensionful roles: `FlightLength`, `FlightDuration`.
- Named-unit projections: `lengthReadout`, `durationReadout`, `speedReadout`, `lengthInMeters`, `durationInSeconds`, `speedInMetersPerSecond`.
- Physical/figure model: `GroundProfileKind`, `FlightHeading`, `FlightDirection`, `FigureFeature`, `RisingGroundFigure`, `RisingGroundFlightSetup`.
- Assumption interfaces: `MatchesProblemAndFigure`, `HasPhysicalFlightParameters`, `SatisfiesHorizontalFlightAndSlopeLaws`.
- Target-side event/answer vocabulary: `IsFirstGroundImpact`, `AnswerChoice`, `AnswerChoice.seconds`, `MatchesAnswerChoice`, `recordedAnswerChoice`.

The blueprint chapter was not edited to add `\leanok` because this task's explicit write permissions prohibit editing blueprint chapters. The plan/dispatcher should add `\leanok` to `thm:physics:phyx_mini_0731:target` after accepting this formalization.

## LeanExplore queries/candidates actually used

- Query `SI physical dimensions quantity length time speed units`: selected `UnitChoices.SI`, `Dimension`, `DimSpeed`, and the dimensional-units infrastructure; `UnitExamples.SpeedEq` was a related dimensional example rather than a trajectory model.
- Query `Dimensionful WithDim DimSpeed`: selected `Dimensionful`; the returned `CarriesDimension.toDimensionful` and `Dimensionful.of_scaleUnit` were supporting rather than needed declarations.
- Queries `WithDim physical dimension tagged value`, `Dimension.L𝓭 Dimension.T𝓭`, and `time physical dimension T𝓭`: selected `WithDim`, `Dimension.L𝓭`, and `Dimension.T𝓭`.
- Queries `DimSpeed one kilometer per hour one meter per second` and `LengthUnit meters kilometers TimeUnit seconds hours`: confirmed `DimSpeed`, `DimSpeed.oneKilometerPerHour`, `DimSpeed.oneMeterPerSecond`, `LengthUnit.kilometers`, `TimeUnit.hours`, and SI readout semantics.
- Query `Real.Angle tangent degrees radians`: selected `Real.Angle` and `Real.Angle.tan`; `Real.tan` was a near miss because the setup retains an angle modulo full turns.
- Query `degrees to Real.Angle constructor`: found the canonical real-to-angle coercion through angle coercion lemmas, but no dedicated degrees constructor, so `angleOfDegrees` performs the standard `degrees * pi / 180` conversion before coercion.
- Queries `constant horizontal velocity position elapsed time kinematics` and `aircraft trajectory collision planar sloping terrain first impact`: returned `ClassicalMechanics.FreeParticle.Trajectory`, `ClassicalMechanics.FreeParticle.velocity_const_of_zero_acc`, and `RigidBodyMotion.velocity`; these are heavier state-space near misses and do not supply the terrain/contact event.
- Query `DimLength DimTime nonnegative dimensionful length duration`: returned the generic `Dimensionful`/dimension infrastructure but no ready-made nonnegative, unit-independent `DimLength` or `DimTime` alias.

Source/module inspection was performed for the candidates used in the file: `Dimensionful` (`Physlib.Units.Basic`), `WithDim` (`Physlib.Units.WithDim.Basic`), `DimSpeed` (`Physlib.Units.WithDim.Speed`), `UnitChoices.SI` (`Physlib.Units.Basic`), `Dimension.L𝓭` and `Dimension.T𝓭` (`Physlib.Units.Dimension`), `LengthUnit.kilometers`, `TimeUnit.hours`, `Real.Angle`, and `Real.Angle.tan`.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `DimSpeed`, `UnitChoices.SI`, `LengthUnit.meters`, `LengthUnit.kilometers`, `TimeUnit.seconds`, `TimeUnit.hours`.
- Mathlib: `Real.Angle`, its coercion from `ℝ`, `Real.Angle.toReal`, `Real.Angle.tan`, `Real.pi`, `Set.Ioo`.

## Local abstractions introduced

- `FlightLength` and `FlightDuration` are not scalar aliases: they specialize Physlib's unit-independent `Dimensionful (WithDim d NNReal)` to the length and time dimensions.
- The trajectory functions in `RisingGroundFlightSetup` preserve distinct physical roles for horizontal distance, aircraft elevation, and ground elevation.
- The local scenario and figure enums retain qualitative prose/image evidence for which no dedicated Physlib object exists.
- `SatisfiesHorizontalFlightAndSlopeLaws` is a faithful interface for constant-speed kinematics, fixed aircraft elevation, and planar-slope geometry; it does not encode the requested result.

## Grounding gaps

- No specialized Mathlib/Physlib API was found for collision of a horizontal aircraft trajectory with an upward planar terrain profile. The free-particle and rigid-body declarations found by LeanExplore require substantially heavier state-space models and do not provide the terrain/contact event, so an explicit trajectory-law interface was used.
- No ready-made `DimLength` or `DimTime` aliases matching this nonnegative, unit-independent use were found; the underlying Physlib representation was specialized directly.
- No dedicated degrees-to-`Real.Angle` constructor was found. `angleOfDegrees` uses Mathlib's grounded coercion from radians and the standard `degrees * pi / 180` conversion.
- The `archon` executable advertised for DAG navigation was not on `PATH`, so no DAG query could be completed. The chapter declares only the single target and the source report lists no previous parts.
- `.archon/AGENTS.md` was absent. The available `.archon/prover-modes/physics-formalize.md` and the task's inline role instructions were followed.

## Verification

- `archon-lean-lsp` diagnostics: success, with only the expected theorem `sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0731.lean`: exit code 0, with only `declaration uses 'sorry'` for `firstGroundImpact_matches_recordedAnswerC`.

## Redraft requests

- None for the physics statement. The blueprint maintainer should only add the prohibited-in-this-task `\leanok` marker after review.
