# Autoformalization result: `problem_phyx_mini_0724.lean`

## Assumption/target split

### Governing laws

- `MatchesIdealWaterPipeScenario` records the textbook applicability conditions: the fluid is water, both pressures use the same atmospheric gauge reference, the flow is steady and incompressible, viscous losses are negligible, and the two marked sections lie on one streamline.
- `SatisfiesCircularRisingPipeGeometry` states that each cross-sectional area is `π (d/2)²` and that the section-2 centreline elevation is the section-1 elevation plus the independently represented vertical rise.
- `SatisfiesIdealPipeFlowLaws.steadyIncompressibleContinuity` states equality of volume flux, `A₁ v₁ = A₂ v₂`.
- `SatisfiesIdealPipeFlowLaws.bernoulliBetweenGaugeTaps` states equality of `p + ρv²/2 + ρgz` at the two marked section centres. It is the unsolved governing relation and contains neither the derived upper speed nor the derived upper pressure constant.
- `UsesTextbookWaterDensityAndGravity` calibrates the water density to `1000 kg/m³` and gravitational acceleration to `9.8 m/s²`. These environmental constants are required to reproduce the recorded option.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the blueprint exposes no dependency on an earlier question part.

### Figure/data readouts

- `MatchesPrimaryPipeFigure` transcribes the section labels `1` and `2`; diameter labels `6.0 cm` and `4.0 cm`; lower speed label `5.0 m/s`; upper symbolic speed label `v₂`; lower gauge label `75 kPa`; upper question-mark gauge; the `2.0 m` rise; left/right and lower/upper ordering; both rightward green arrows; both section-centre dots, gauge taps, and diameter arrows; the water-filled pipe; and the narrowing rising connector.
- `MatchesProblemReadouts` assigns only the five supplied scalar readouts: the two diameters, lower speed, lower gauge pressure, and vertical rise. It assigns no numerical value to the upper speed or upper gauge pressure.
- `displayedGaugePressureKilopascals` records choices A–D as `4.4`, `4.8`, `4.6`, and `5.0 kPa`. It does not state which choice follows from the physics.

### Current target conclusions

- `upper_speed_from_continuity` derives `v₂ = 45/4 m/s` from the diameter readouts, circular geometry, and continuity.
- `upper_gauge_pressure_in_pascals` derives `p₂ = 18475/4 Pa` from the readouts, calibration, geometry, continuity, and Bernoulli equation.
- `problem_phyx_mini_0724` concludes the exact equivalent readouts `18475/4 Pa = 739/160 kPa` and that the physical reading uniquely rounds to choice C, `4.6 kPa`.

## Goal-faithfulness audit

`RisingPipeSetup.stateAt .two` contains independent `speed` and `gaugePressure` fields. They are not definitions and are not initialized from `45/4`, `18475/4`, `739/160`, `4.6`, or choice C. The upper speed and pressure are constrained only through the same generic continuity and Bernoulli laws that also contain the lower-section observables.

The figure premise explicitly represents the upper labels as `v₂` and `?`; the numerical readout premise omits both unknown values. The water/gravity calibration fixes only environmental parameters. Circular geometry gives areas from the two supplied diameters, and the elevation equation gives only the supplied rise. None of these structures contains the solved upper pressure formula or answer label.

`RoundsToNearestTenthKilopascal`, `MatchesDisplayedUpperGaugePressure`, and `IsUniqueMatchingUpperGaugePressure` are generic comparison predicates against all four displayed alternatives. They do not force any alternative to match by unfolding. Therefore a later proof must derive the upper speed, substitute it into Bernoulli's equation, calculate the exact pressure, establish the rounding inequality, and exclude all other choices.

## Declarations created and blueprint correspondence

All declarations are in `PhyXMiniProblems.ProblemPhyXMini0724`.

- Dimension layer: `massDensityDimension`, `accelerationDimension`, `LengthQuantity`, `MassDensityQuantity`, `AccelerationQuantity`, and the seven named-unit readout functions.
- Physical/figure vocabulary: `PipeSection`, `FluidKind`, `PressureReference`, `HorizontalFigureLocation`, `VerticalFigureLocation`, `HorizontalFlowDirection`, and `WaterPipeFigure`.
- Independent physical model: `PipeSectionState` and `RisingPipeSetup`.
- Premise families: `MatchesIdealWaterPipeScenario`, `MatchesPrimaryPipeFigure`, `MatchesProblemReadouts`, `UsesTextbookWaterDensityAndGravity`, `SatisfiesCircularRisingPipeGeometry`, and `SatisfiesIdealPipeFlowLaws`.
- Answer presentation: `AnswerChoice`, `displayedGaugePressureKilopascals`, `RoundsToNearestTenthKilopascal`, `MatchesDisplayedUpperGaugePressure`, and `IsUniqueMatchingUpperGaugePressure`.
- Derived declarations: `upper_speed_from_continuity`, `upper_gauge_pressure_in_pascals`, and main theorem `problem_phyx_mini_0724`.
- `PhyXMiniProblems.ProblemPhyXMini0724.problem_phyx_mini_0724` corresponds to blueprint label `thm:physics:phyx_mini_0724:target`.

The two derived lemmas and main theorem have the required autoformalization-stage `by sorry` bodies.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

Queries run:

- `Bernoulli equation for steady incompressible fluid flow through a pipe`
- `fluid continuity equation cross-sectional area times velocity constant`
- `DimPressure pressure pascal kilopascal`
- `DimSpeed speed metres per second`
- `DimLength length metre centimetre`
- `mass density Dimensionful fluid density`
- `DimArea physical area square metre`
- `DimAcceleration acceleration metre per second squared`
- `DimLength physical length Dimensionful WithDim`
- `UnitChoices.SI Dimensionful WithDim coherent SI readout`

Candidates whose source and module were inspected:

- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`.
- `DimPressure` and `DimPressure.pascal` from `Physlib.Units.WithDim.Pressure`.
- `DimSpeed` and `DimSpeed.oneMeterPerSecond` from `Physlib.Units.WithDim.Speed`.
- `DimArea` and `DimArea.squareMeter` from `Physlib.Units.WithDim.Area`.
- `LengthUnit.centimeters` from `Physlib.SpaceAndTime.Space.LengthUnit`.
- `FluidDynamics.MassDensity` from `Physlib.FluidDynamics.FluidState`.
- `FluidDynamics.NavierStokes.ClassicalContinuityEquation` and `FluidDynamics.NavierStokes.SmoothContinuityEquation` from `Physlib.FluidDynamics.NavierStokes.Continuity`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, `DimPressure`, `DimSpeed`, and `DimArea`.
- Mathlib/core: `NNReal`, `ℝ`, `Real.pi`, exact rational arithmetic, absolute-value notation, strings, booleans, and finite inductive types.

## Local abstractions introduced

- `LengthQuantity`, `MassDensityQuantity`, and `AccelerationQuantity` specialize Physlib's unit-independent `Dimensionful (WithDim _ NNReal)` machinery to the physical roles needed here. They are not transparent scalar aliases: a coherent unit choice is required before obtaining a real readout.
- `WaterPipeFigure` preserves the actual raster evidence separately from physical laws, including the unknown upper gauge and symbolic `v₂` label.
- `PipeSectionState` keeps diameter, area, elevation, speed, and gauge pressure as distinct physical observables at each marked section.
- `SatisfiesCircularRisingPipeGeometry` is the minimal geometric bridge between the labelled diameters and the cross-sectional areas used by continuity.
- `SatisfiesIdealPipeFlowLaws` is the minimal lumped two-section interface for continuity and Bernoulli flow. Its scalar equations use coherent SI projections of dimensionful quantities, so every sum and product is dimensionally homogeneous.

## Grounding gaps and redraft requests

- LeanExplore found no direct Bernoulli-equation declaration in Mathlib/Physlib.
- Physlib's available continuity declarations are PDE field equations on a `FluidState`; they do not directly express the two-section lumped relation `A₁v₁ = A₂v₂`. The faithful local law interface was used instead of forcing the problem into an unrelated PDE setup.
- `FluidDynamics.MassDensity d` is a spatial scalar field, not a unit-independent lumped density quantity. Physlib also exposed no ready-made `DimLength` or `DimAcceleration` alias in the search results. The local dimension specializations preserve those roles.
- The problem/blueprint does not explicitly state the idealizations needed for Bernoulli, the water density, or the value of gravitational acceleration. The formalization makes them explicit. A blueprint redraft should record steady incompressible negligible-loss flow, `ρ = 1000 kg/m³`, and the adopted `g = 9.8 m/s²` calibration.
- The requested `.archon/AGENTS.md` is absent. The available `.archon/prover-modes/physics-formalize.md` and the explicit task instructions were followed.
- The assigned Lean file did not exist, so there were no pre-existing `/- USER: ... -/` hints to preserve.
- The chapter exists and is marked `% archon:physics`, but its theorem environment has no `\lean{...}` mapping. The explicit write-permission block makes blueprint chapters read-only for this task, so a blueprint-writing agent should add `\lean{PhyXMiniProblems.ProblemPhyXMini0724.problem_phyx_mini_0724}` and the appropriate `\leanok` marker.

## Verification

- The primary raster `phyx_data/test_image/724.png` was inspected directly and treated as authoritative over the auxiliary caption.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0724.lean` exited successfully with exactly three expected `declaration uses sorry` warnings and no errors.
