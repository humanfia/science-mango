# Autoformalization result: `problem_phyx_mini_0836.lean`

## Assumption/target split

### Governing laws

- `SatisfiesUniformParallelPlateFieldModel` states that the field points from the positive lower plate to the negative upper plate, while the negative electron's force and acceleration point downward; it also relates the dimensionful scalar field-strength readout to the norm of `Electromagnetism.ElectricField 3` throughout the capacitor interior.
- `SatisfiesConstantElectricAccelerationKinematics` states the uniform-horizontal-motion and constant-downward-acceleration endpoint equations for launch and landing at the same height.
- `SatisfiesElectricForceLaw` states the magnitude form of Newton's second law plus the electric Lorentz force, `m a = |q| E`.
- `HasPhysicalParameters` supplies positivity/non-vacuity conditions needed by later proofs, without fixing the requested field value.

### Previous-part results

- None. The source report has no previous parts.

### Figure/data readouts

- `MatchesProblemAndFigureReadouts` records the electron species and negative charge sign, initial speed `5 * 10^6 m/s`, launch angle `π/4` (and the displayed `45°`), same-plate horizontal range `4 cm = 4/100 m`, the `v₀` arrow, dashed parabolic arc, and the parallel plates' polarities and directions.
- The raster was treated as primary evidence: it shows positive marks on the lower plate and teal negative marks on the upper plate. This corrects the auxiliary caption's statement that the upper plate is unmarked.
- `UsesElectronReferenceConstants` calibrates the dimensionful electron mass and charge magnitude to `electronRestMassInKilograms` and Physlib's `ChargeUnit.elementaryCharge` readout.
- `ParallelPlateFigure` and `CapacitorElectronSetup` also retain the plate separation, flight duration, capacitor interior, actual spacetime electric field, launch/landing labels, and relevant directions even where these do not occur in the final closed form.

### Current target conclusions

- `electricFieldStrength_eq_mass_mul_speed_sq_div_charge_mul_range` concludes the derived SI relation `E = m v₀² / (|q| R)`.
- `electricFieldStrength_rounds_to_threePointSixTimesTenCubed` concludes that the independent field-strength readout is within `50 N/C` of `3.6 * 10^3 N/C`.
- `problem_phyx_mini_0836` concludes both that tolerance statement and that the modeled field matches recorded answer choice D.

## Goal-faithfulness audit

The electric-field strength is an independent dimensionful field of `CapacitorElectronSetup`; it is not defined from the recorded answer. No premise fixes it to `3.6 * 10^3 N/C`, asserts choice D matches, states the derived `E = m v₀²/(|q|R)` formula, or includes either target tolerance. The governing structures contain only direction/uniformity, endpoint kinematics, positivity, reference calibrations, and `m a = |q| E`. `AnswerMatchesElectricField` merely defines what agreement with a displayed choice means and still requires the substantive numerical bound to prove it. Thus the requested answer remains entirely on the conclusion side.

The scalar equations are explicit coherent-SI readouts of dimensionful quantities. This preserves the physical dimensions while allowing the later prover to use real algebra. The target is a rounding claim because the answer choices are given to two significant figures; the exact calculation is approximately `3.55 * 10^3 N/C`, so literal equality to `3.6 * 10^3` would misstate the physics.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0836:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0836.problem_phyx_mini_0836`.
- Supporting target lemmas: `electricFieldStrength_eq_mass_mul_speed_sq_div_charge_mul_range` and `electricFieldStrength_rounds_to_threePointSixTimesTenCubed`.
- Physical quantity/readout declarations: `accelerationDimension`, `electricFieldStrengthDimension`, the `*Quantity` abbreviations, and the named-unit/SI readout functions.
- Apparatus/model declarations: direction/species/plate/trajectory/model inductives, `ParallelPlateFigure`, and `CapacitorElectronSetup`.
- Assumption declarations: `MatchesProblemAndFigureReadouts`, `UsesElectronReferenceConstants`, `HasPhysicalParameters`, `SatisfiesUniformParallelPlateFieldModel`, `SatisfiesConstantElectricAccelerationKinematics`, and `SatisfiesElectricForceLaw`.
- Answer-display declarations: `AnswerChoice`, `answerStrengthInNewtonsPerCoulomb`, `answerRoundingTolerance`, `recordedDatasetAnswer`, and `AnswerMatchesElectricField`.
- The blueprint environment is ready for `\leanok`; it was not edited because this prover's explicit write permissions restrict edits to the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `electric field force on a charged particle Newton second law`: considered `Electromagnetism.ElectricField` and `UnitExamples.NewtonsSecondWithDim`; the former was used, while the latter grounded the dimensional form of `F = m a` but was not directly reusable for this setup.
- Natural-language query `projectile motion constant acceleration equal-height range launch angle`: no matching projectile law was returned; the leading results were near misses such as `RigidBodyMotion` and `RigidBodyMotion.displacement`.
- Natural-language query `Dimensionful WithDim SI units mass charge speed electric field strength`: returned `UnitChoices.SI` and electromagnetic field declarations and grounded the coherent-unit readout design.
- Likely-name query `ChargeUnit.elementaryCharge LengthUnit.centimeters DimSpeed Electromagnetism.ElectricField`, followed by the individual queries `Dimensionful`, `WithDim`, `DimSpeed`, and `ChargeUnit.elementaryCharge`: used those exact declarations after fetching their source signatures.
- Likely-name query `MassUnit.kilograms TimeUnit.seconds`: grounded `MassUnit.kilograms` and `UnitChoices.SI`; the imported time-unit API supplies `TimeUnit.seconds` used in the compiled file.
- Source was fetched for `Dimensionful`, `WithDim`, `DimSpeed`, `Electromagnetism.ElectricField`, `ChargeUnit.elementaryCharge`, `LengthUnit.centimeters`, `UnitChoices.SI`, and the near-miss `UnitExamples.NewtonsSecondWithDim` before retaining the local model interfaces.

## PhysLean/Mathlib names grounded

- PhysLean: `Dimensionful`, `WithDim`, `DimSpeed`, `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `Dimension.C𝓭`, `UnitChoices.SI`, `LengthUnit.meters`, `LengthUnit.centimeters`, `TimeUnit.seconds`, `MassUnit.kilograms`, `ChargeUnit.coulombs`, `ChargeUnit.elementaryCharge`, `Electromagnetism.ElectricField`, `Time`, and `Space`.
- Mathlib: `NNReal`, `EuclideanSpace`, `Set`, `Real.pi`, `Real.sin`, `Real.cos`, and the norm notation used for the field vector.

## Local abstractions introduced

- `accelerationDimension` and `electricFieldStrengthDimension` make the derived dimensions explicit rather than treating accelerations or fields as bare reals.
- Typed quantity abbreviations use PhysLean's unit-independent `Dimensionful (WithDim ...)` infrastructure; they are not transparent scalar aliases.
- The apparatus and figure inductives/structures distinguish physical roles (particle species, charge sign, plate polarity, directions, trajectory style, and motion idealization) that are not represented by a single existing library object.
- The three `Satisfies...` structures faithfully expose the missing elementary projectile/electric-force laws as assumptions without including any current target conclusion.
- `electronRestMassInKilograms` is a calibrated scalar reference readout because LeanExplore found no library electron-rest-mass constant; the setup's mass itself remains dimensionful.

## Grounding gaps

- No Mathlib/PhysLean declaration matching equal-height projectile endpoint kinematics under constant acceleration was found, so `SatisfiesConstantElectricAccelerationKinematics` states those laws locally.
- No directly applicable nonrelativistic point-particle law combining electric force magnitude and Newton's second law was found, so `SatisfiesElectricForceLaw` states `m a = |q| E` locally.
- `Electromagnetism.ElectricField` supplies the spacetime vector field but carries no `WithDim` tag. The setup therefore retains that field and separately stores a dimensionful scalar strength, with `uniformMagnitude` connecting its SI readout to the vector norm.
- The `archon dag-query` executable was not available on this lane's shell `PATH`; the blueprint has no declared ancestors or previous parts, so this did not block the formalization.

## Verification

- `archon-lean-lsp` diagnostics: three expected `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0836.lean`: exit code 0 with exactly the same three expected warnings.

## Retry-gate resolution

The iteration-001 gate reason was evidence-only: it reported that no genuine
post-formalization result existed. This report is based on the completed Lean
model, the primary raster, the source report, and the actual LeanExplore and
compiler checks listed above, so it supplies the missing post-formalization
evidence without changing or weakening the physical target.
