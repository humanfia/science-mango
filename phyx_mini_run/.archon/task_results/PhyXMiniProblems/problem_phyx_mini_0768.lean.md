# Autoformalization result: `problem_phyx_mini_0768.lean`

## Assumption/target split

### Governing laws

- `SatisfiesInitialVelocityGeometry` states that the cart's signed horizontal velocity is the negative of its stated speed and decomposes the package's chute-exit speed into `x` and `y` components using the `37 degree` incline. It also relates the speed magnitude to the Euclidean norm of the exit-velocity vector.
- `UsesStandardNearEarthGravity` states zero horizontal acceleration and vertical acceleration `-9.8 m/s²`.
- `SatisfiesProjectileMotion` states the constant-acceleration endpoint position and velocity equations in every coherent unit system.
- `SatisfiesInelasticCaptureLaws` states conservation of horizontal momentum during the short capture and the generic relation between final speed and the magnitude of the common horizontal velocity. It deliberately does not assert vertical momentum conservation, since the floor supplies a vertical impulse.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemReadouts` records cart mass `50 kg`, package mass `15 kg`, initial cart speed `5 m/s`, chute-exit package speed `3 m/s`, chute-exit height `4 m`, and chute angle `37 degrees`.
- `MatchesQualitativeScenario` records negligible drag with constant near-Earth gravity, a frictionless floor, and a captured package rolling together with the cart.
- `MatchesPrimaryFigure` records the inclined chute, orange package, open cart, floor, vertical height arrow, angle arc, the `37 degrees` and `4.00 m` labels, the down-right package arrow, the leftward cart arrow, and the relative schematic locations visible in `768.png`.
- The primary raster `phyx_data/test_image/768.png` was inspected directly in this iteration and confirms those directions, labels, and relative locations.
- `MatchesPhysicalGeometry` connects the physical chute exit, landing position, cart bottom, and the dimensionful `4 m` vertical separation.
- `HasPhysicalParameters` selects the positive and directional branch shown in the figure without assigning a numerical final speed.

### Current target conclusions

- `package_horizontal_velocity_at_impact`: the package's impact `x` velocity is `3 cos(37 degrees) m/s`.
- `common_final_horizontal_velocity_exact`: the common signed horizontal velocity is the mass-weighted horizontal-momentum quotient.
- `final_cart_speed_after_package_capture`: the final cart speed is the absolute value of that quotient, rounds to `3.29 m/s`, and uniquely selects choice B.

## Goal-faithfulness audit

The unknown `finalCartSpeed` and `commonFinalHorizontalVelocity` are independent fields of `ShippingCartCaptureSetup`; neither is defined from an answer choice or from the solved quotient. No source-data, figure, geometry, qualitative-scenario, or positivity premise contains `3.29`, choice B, or the final quotient. The only premise mentioning final speed is the general physical identity that speed is the magnitude of signed velocity. The only premise mentioning common final velocity is the general horizontal momentum balance. Therefore the numerical conclusion still requires projectile horizontal-velocity conservation, chute geometry, problem readouts, momentum conservation, and taking a magnitude.

The setup retains the seemingly extraneous `4 m` height and flight time because they are part of the physical scenario and determine the vertical impact state. They are not used to fake the horizontal answer. The formalization also avoids the physically false claim that total vertical momentum is conserved through capture.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0768:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0768.final_cart_speed_after_package_capture`.
- Supporting declarations are `package_horizontal_velocity_at_impact` and `common_final_horizontal_velocity_exact`.
- The named-unit and figure interfaces are contained in namespace `PhyXMiniProblems.ProblemPhyXMini0768`.
- The blueprint chapter already existed. It was not edited because this task's explicit write permissions prohibit editing blueprint chapters; an authorized blueprint agent should add `\leanok` to the target environment.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]` as required.

- `dimensionful physical quantity coherent unit choices WithDim`: adopted `Dimensionful`; its source in `Physlib.Units.Basic` confirms that it is a unit-choice-indexed quantity satisfying the library's dimensional scaling law.
- `DimSpeed physical speed quantity`: adopted `DimSpeed`; its source in `Physlib.Units.WithDim.Speed` is `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `UnitChoices.SI`: adopted `UnitChoices.SI`; its inspected source selects metres, seconds, kilograms, coulombs, and kelvin.
- `MassUnit LengthUnit TimeUnit`: adopted the three named-unit types used at readout boundaries; the `MassUnit`, `LengthUnit`, and `TimeUnit` sources were inspected.
- `WithDim Dimension L𝓭 T𝓭 M𝓭`: adopted `WithDim`, `Dimension`, and the foundational dimension constants; the `WithDim` and `Dimension` sources/modules were inspected.
- `perfectly inelastic collision horizontal momentum conservation cart projectile`: considered `ClassicalMechanics.FreeParticle.linearMomentum_conserved_of_velocity_const`, `ClassicalMechanics.FreeParticle.linearMomentum_conserved`, `RigidBodyMotion.linearMomentum`, and `Momentum`. These results/types do not package an impulsive cart-plus-projectile capture constrained to conserve only horizontal momentum, so a local law interface was retained.
- `constant acceleration projectile endpoint velocity position`: the returned free-particle and rigid-body velocity declarations do not state the elementary finite-time constant-acceleration endpoint equations needed here, so those equations remain a local governing-law interface.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `DimSpeed`, `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `UnitChoices`, `UnitChoices.SI`, `MassUnit`, `LengthUnit`, and `TimeUnit`.
- Mathlib: `EuclideanSpace ℝ (Fin 2)`, `NNReal`, `Real.pi`, `Real.sin`, `Real.cos`, Euclidean norm notation `‖·‖`, and absolute-value notation `|·|`.

## Local abstractions introduced

- Dimensionful aliases for mass, length, time, signed velocity, planar position, planar velocity, and planar acceleration are built from Physlib's unit-independent `Dimensionful (WithDim ...)` infrastructure; they are not aliases to bare scalars.
- `ShippingCartFigure` preserves the literal image vocabulary, arrow directions, height endpoints, and schematic relations without treating raster coordinates as physical metre measurements.
- `ShippingCartCaptureSetup` separates independent observables and intermediate states from source premises and governing laws.
- `SatisfiesInitialVelocityGeometry`, `SatisfiesProjectileMotion`, and `SatisfiesInelasticCaptureLaws` are the smallest local law interfaces needed because no LeanExplore result represented this combined chute-flight-capture process.
- `RoundsToNearestHundredth`, `MatchesAnswerChoice`, and `IsUniqueClosestDisplayedChoice` distinguish the exact trigonometric result from the rounded multiple-choice display.

## Grounding gaps

- No Mathlib/Physlib declaration was found for a perfectly inelastic capture of a projectile by a horizontally constrained cart with conservation of only the horizontal momentum component. The local law predicate states that physical law directly rather than guessing an API or assuming the requested numerical answer.
- No current-project `.archon/AGENTS.md` was present. The complete `.archon/prover-modes/physics-formalize.md` role file and the matching `PROGRESS.md` entry were used instead.
- The assigned Lean file did not exist initially, so the required `/- USER: ... -/` absence note was added to the created file.
- The `archon` executable advertised for optional DAG navigation was not available on `PATH`; the blueprint chapter and target label remained the source of truth.
- No blueprint redraft is requested. The only follow-up is the permission-separated addition of `\leanok` by a blueprint-authorized agent.

## Verification

- `archon-lean-lsp` diagnostics: no errors; three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0768.lean`: exit code `0`; the same three expected warnings only.
