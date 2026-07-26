## Assumption/target split

### Governing laws

- `SatisfiesSpillingColumnGeometry.depthIsTopRimMinusPistonElevation` states that, while water spills at the open rim, the water depth above a piston at elevation `h` is `H - h` in every coherent unit system.
- `SatisfiesHydrostaticPressureLaw.waterPressureAtPiston` states the hydrostatic relation between ambient pressure at the open free surface and the independent water pressure on the piston, using the independent water-column depth.
- `SatisfiesThinPistonForceBalance.verticalPressureForcesBalance` states equality of upward air force and downward water-pressure force, retaining the common piston area `A` explicitly.
- `HasPhysicalSpillingWaterParameters` supplies positivity of `H`, `A`, `ρ`, `g`, and `P₀`, including the nonzero area needed for later force-balance cancellation.

### Previous-part results

- None. The source is a standalone question.

### Figure/data readouts

- `PistonCylinderFigure` and `MatchesSuppliedPistonCylinderFigure` encode the primary raster `phyx_data/test_image/665.png`: visible labels `H`, `h`, `g`, and `Air`; `H` from the bottom datum to the open rim; `h` from the bottom datum to the piston plane; downward gravity; water above a horizontal piston; and a valved air line entering below it.
- `MatchesSpillingWaterScenario` records water, supplied air, a thin/frictionless/negligible-weight piston, and continued spillover at the rim.
- `IsAdmissiblePistonElevation` restricts the variable piston elevation to `0 ≤ h ≤ H`.
- `displayedPressureFormula` transcribes choices A--D as presentation data. No answer formula is used as a premise.

### Current target conclusions

- `problem_phyx_mini_0665` concludes, for every coherent choice of units,
  `P_air(h) = P₀ + (H - h) ρ g`.
- `answerChoiceD_isCorrect` concludes that this physical pressure agrees with displayed choice D.

## Goal-faithfulness audit

The target air pressure is an independent field `airPressureUnderPiston`; it is not defined from `H`, `h`, `ρ`, `g`, or `P₀`. The governing interfaces also do not state the target formula: geometry relates only column depth to `H - h`, hydrostatics relates only water-side pressure to the independent depth, and force balance relates the two independent pressure forces through area `A`. Deriving the target therefore requires combining all three laws and cancelling a strictly positive area. The choice table merely transcribes the problem's printed options and is not referenced by the main theorem statement.

## Declarations created and blueprint labels

- Blueprint `thm:physics:phyx_mini_0665:target` → `PhyXMiniProblems.ProblemPhyXMini0665.problem_phyx_mini_0665`.
- Supporting conclusion: `PhyXMiniProblems.ProblemPhyXMini0665.answerChoiceD_isCorrect`.
- Supporting physical/model declarations: dimension/readout definitions; primary-figure enums and `PistonCylinderFigure`; `SpillingWaterPistonSetup`; scenario, figure, positivity, geometry, hydrostatic, and force-balance predicates; and the answer-choice transcription.
- The target blueprint theorem environment is ready for `\leanok`. It was not edited because the prover write permissions explicitly prohibit blueprint edits; marker synchronization/review should apply it.

## LeanExplore queries/candidates actually used

- Query `hydrostatic pressure fluid column density gravity depth`: candidate `DimPressure`; near-miss `FluidDynamics.FluidState`.
- Query `pressure force area dimensional physical quantity`: candidates `DimArea`, `DimPressure`, `Dimension`, and `WithDim`; near-miss `FluidDynamics.BodyForce`.
- Query `SI dimensions pressure density acceleration length`: candidates `UnitChoices.SI`, `DimPressure`, and `Dimension.L𝓭`.
- Query `hydrostaticPressure`: no hydrostatic-equilibrium theorem was returned; results were pressure types and general fluid-state declarations.
- Queries `DimLength DimMassDensity DimAcceleration`, `DimDensity`, `mass density dimension`, and `DimForce`: candidates `Dimension.L𝓭`, `WithDim`, and `FluidDynamics.MassDensity`; no unit-independent scalar aliases for length, uniform mass density, acceleration, or force matched the needed role.
- Source/module/docstring were fetched for `DimPressure`, `DimArea`, `UnitChoices.SI`, `WithDim`, `Dimension.L𝓭`, `FluidDynamics.MassDensity`, `FluidDynamics.FluidState`, and `FluidDynamics.FluidInMomentumBalance` before selecting the used APIs.

## PhysLean/Mathlib names grounded

- Used from Physlib: `DimPressure`, `DimArea`, `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Used from Mathlib: `NNReal`/`ℝ≥0` for nonnegative magnitudes and `ℝ` for signed coherent-unit readouts and pressures.
- `FluidDynamics.MassDensity` and `FluidDynamics.FluidState` were not used because they are real-valued spacetime fields without the unit-independent dimension tagging needed for this uniform static setup.

## Local abstractions introduced

- `LengthQuantity`, `MassDensityQuantity`, and `AccelerationQuantity` are `Dimensionful (WithDim ... NNReal)` types, following the same Physlib design as `DimArea`/`DimPressure`; they preserve dimension and unit-change behavior rather than aliasing physical primitives to scalars.
- `massDensityDimension = M𝓭 L𝓭⁻³` and `accelerationDimension = L𝓭 T𝓭⁻²` supply the missing dedicated quantity names.
- `SatisfiesSpillingColumnGeometry`, `SatisfiesHydrostaticPressureLaw`, and `SatisfiesThinPistonForceBalance` are local law interfaces because no matching hydrostatic/piston-balance declaration was found. Their separation preserves the physical derivation and keeps the requested formula out of assumptions.

## Grounding gaps

- LeanExplore/Physlib provided dimensional pressure and area types but no ready-made hydrostatic law or static piston pressure-force balance compatible with this symbolic school-level model.
- `.archon/AGENTS.md` was absent in this workspace. The available `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`, and the archived project role conventions were followed; no task-blocking role ambiguity remained.
- No blueprint redraft is requested. The chapter accurately identifies the scenario and recorded answer, though its generated caption understated that the source raster visibly contains a piston and open top; the Lean figure transcription follows the raster itself.

## Verification

- `archon-lean-lsp` diagnostics: success, with only two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0665.lean`: exit code 0, with the same two expected warnings.
