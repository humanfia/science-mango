# Autoformalization result: `problem_phyx_mini_0765.lean`

Post-formalization review regenerated for Archon iteration 003. The gate's
recorded defect was missing evidence, not a semantic defect in the revised
Lean model, so the declaration statements were preserved.

## Assumption/target split

### Governing laws

- `SatisfiesStaticSpringEquilibrium`: in every coherent choice of mass, length, and time units, the frame-only Hooke force `k x₀` balances the frame weight `m_f g`.
- `SatisfiesFreeFallLaw`: the putty obeys the constant-gravity relation `v² = v₀² + 2 g h` during its fall from the displayed release level to the frame platform.
- `SatisfiesImpulsiveStickingCollision`: one-dimensional downward momentum is conserved during the short completely inelastic impact. Mechanical energy is deliberately not assumed across this collision.
- `SatisfiesMaximumDisplacementGeometry`: the spring extension at the later turning point is the frame-only equilibrium extension plus the downward displacement measured from that old equilibrium.
- `SatisfiesPostImpactMechanicalEnergy`: after impact, the combined frame and putty conserve kinetic plus spring plus gravitational energy up to the turning point. Downward is positive, so the gravitational-potential change is `-M g y`.
- `MatchesInitialAndTurningPointConditions`: the putty is released from rest, the frame is at rest immediately before impact, and the combined body is instantaneously at rest at the maximum downward displacement.
- `HasPhysicalInputParameters`: only independent input masses, equilibrium extension, drop height, gravity magnitude, and spring stiffness are required positive.

### Previous-part results

- None. The source report records `previous_parts: []`, and the blueprint declares no dependency labels.

### Figure/data readouts

- Prose measurements: frame mass `0.150 kg = 3/20 kg`, putty mass `0.200 kg = 1/5 kg`, frame-only equilibrium spring extension `0.0400 m = 1/25 m`, and drop height `30.0 cm = 0.300 m`.
- Primary image 765: a fixed upper support, vertical coil spring, suspended frame, horizontal receiving platform at the frame bottom, red putty above the platform, and a vertical double-headed arrow labelled `30.0 cm` between the putty's initial level and the platform.
- Qualitative model readouts: ideal massless Hookean spring, putty sticking to the frame, an impact impulsive relative to the spring motion, and undamped post-impact vertical motion.
- `MatchesProblemAndFigureReadouts` encodes these quantities and observations. The four displayed choices are stored separately as `0.371`, `0.199`, `0.085`, and `0.264` metres; the dataset's label B is preserved only as metadata.

### Current target conclusions

- Derived displacement quadratic:
  `2625 y² - 280 y - 48 = 0`, where `y` is the metre readout of the maximum downward displacement from the old equilibrium.
- Exact physical root:
  `y = (28 + 8 * Real.sqrt 91) / 525`.
- Printed-precision result: this root is approximately `0.198695497359 m`, hence it rounds to `0.199 m` within half a millimetre and makes B the unique closest displayed choice.

## Goal-faithfulness audit

No premise, setup field constraint, governing-law field, or local definition states the exact root, the value `0.199 m`, or the choice B. `VerticalSpringPuttySetup.maximumDownwardDisplacement` is an unconstrained dimensionful length. Its only premise-side characterization is physical: it is measured from the old equilibrium, gives the spring extension at the turning point, and has zero turning-point speed. Together with the energy law and the nonnegative carrier `NNReal`, this selects the physical positive root rather than defining the answer.

The spring stiffness is not supplied as hidden numerical data; it must be calibrated from the given frame mass and static extension. The impact speed and common post-impact speed are likewise unconstrained setup quantities determined only through free fall and momentum conservation. Energy conservation is asserted only after the inelastic impact. Thus the multi-stage physics remains substantive, and all requested numerical relations stay on the conclusion side.

`recordedDatasetAnswer := .B` preserves source metadata but is not accepted by any theorem as a hypothesis and does not make `MatchesAnswerChoice` or `IsUniqueClosestDisplayedChoice` true by unfolding.

## Declarations created

- Blueprint label `thm:physics:phyx_mini_0765:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0765.problem_phyx_mini_0765`.
- Derived lemmas:
  - `springStiffness_calibrated_by_static_extension`
  - `putty_impact_speed_squared`
  - `common_speed_immediately_after_impact`
  - `maximumDownwardDisplacement_quadratic`
  - `maximumDownwardDisplacement_exact`
- Dimensionful quantities/readouts:
  - `MassQuantity`, `LengthQuantity`, `SpeedQuantity`
  - `AccelerationMagnitudeQuantity`, `SpringStiffnessQuantity`
  - coherent generic readouts and SI convenience readouts for kilograms, metres, centimetres, metres per second, metres per second squared, and newtons per metre
- Physical/figure vocabulary:
  - `FigureObject`, `FigureLabel`, `FigureLevel`, `Orientation`
  - `SpringModel`, `CollisionOutcome`, `CollisionTimeScale`, `PostImpactMotionModel`
  - `SuppliedVerticalSpringFigure`, `VerticalSpringPuttySetup`
- Premise interfaces:
  - `MatchesProblemAndFigureReadouts`
  - `MatchesInitialAndTurningPointConditions`
  - `HasPhysicalInputParameters`
  - the five governing-law/geometry structures listed above
- Answer vocabulary:
  - `AnswerChoice`, `displayedDistanceInMeters`, `recordedDatasetAnswer`
  - `RoundsToNearestMillimeter`, `MatchesAnswerChoice`, `IsUniqueClosestDisplayedChoice`

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Dimensionful WithDim physical quantity with unit choices mass length`: returned `Dimensionful`, `UnitChoices`, `Dimension`, and `CarriesDimension.toDimensionful`. `Dimensionful` and `UnitChoices` were selected.
- Likely-name query `DimSpeed speed quantity`: returned and confirmed `DimSpeed` and its named-unit examples. `DimSpeed` was selected for vertical speed magnitudes.
- Likely-name queries `WithDim` and `Dimension.L𝓭 Dimension.M𝓭 Dimension.T𝓭`: confirmed `WithDim` and the length, mass, and time dimension generators used to assemble the remaining physical quantity types.
- Unit queries `MassUnit LengthUnit TimeUnit`, `UnitChoices.SI`, and `MassUnit.kilograms LengthUnit.meters LengthUnit.centimeters TimeUnit.seconds`: confirmed the unit types, SI base choice, and every named-unit constructor used by the scalar readouts.
- Likely-name query `DimAcceleration`: returned `FluidDynamics.NavierStokes.materialAcceleration`, harmonic-oscillator trajectory acceleration, and general dimension machinery, but no `DimAcceleration` physical-magnitude type. This grounded the decision to construct acceleration from `WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)`.
- Natural-language query `inelastic collision momentum conservation Hooke spring mechanical energy free fall`: returned `ClassicalMechanics.FreeParticle.linearMomentum`, `ClassicalMechanics.FreeParticle.linearMomentum_conserved`, `ClassicalMechanics.HarmonicOscillator.energy`, `ClassicalMechanics.HarmonicOscillator.energy_conservation_of_equationOfMotion`, and `Momentum`. Their sources show that they concern a free particle or a smooth harmonic-oscillator trajectory, not the problem's two-body sticking impact followed by a gravity-shifted spring stage; they were assessed as near-misses rather than forced into the model.
- Natural-language query `real square root Real.sqrt` found the square-root inequality API; exact likely-name query `Real.sqrt` returned `Real.sqrt`, which was selected for the exact positive root.

Source and module information was fetched for the candidates actually used:
`Dimensionful` (`Physlib.Units.Basic`), `WithDim`
(`Physlib.Units.WithDim.Basic`), `DimSpeed`
(`Physlib.Units.WithDim.Speed`), `UnitChoices.SI`
(`Physlib.Units.Basic`), and `Real.sqrt`
(`Mathlib.Analysis.Real.Sqrt`). Source was also inspected for the mechanics
near-misses `Momentum`, `ClassicalMechanics.FreeParticle.linearMomentum`,
`ClassicalMechanics.FreeParticle.linearMomentum_conserved`,
`ClassicalMechanics.HarmonicOscillator.energy`, and
`ClassicalMechanics.HarmonicOscillator.energy_conservation_of_equationOfMotion`.

## Physlib/Mathlib names grounded

- Physlib:
  - `Dimensionful` from `Physlib.Units.Basic`
  - `WithDim` from `Physlib.Units.WithDim.Basic`
  - `DimSpeed` from `Physlib.Units.WithDim.Speed`
  - `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`
  - `UnitChoices.SI`, `MassUnit.kilograms`, `LengthUnit.meters`, `LengthUnit.centimeters`, and `TimeUnit.seconds`
- Mathlib:
  - `NNReal`, real absolute-value notation, and `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt`

## Local abstractions introduced

- Acceleration magnitude is represented as `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)`, and spring stiffness as `Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)`. These preserve the exact physical dimensions instead of using scalar aliases.
- Figure-object, label, level, orientation, impact-outcome, and idealization inductives preserve roles and primary-image evidence not covered by a matching library object.
- The setup stores genuinely physical quantities independently of unit readouts. Scalars appear only after selecting coherent units.
- The static-equilibrium, free-fall, impulsive-momentum, extension-geometry, and post-impact-energy structures are narrow law interfaces for the missing combined model. They state standard unsolved laws and contain no answer-specific relation.

## Grounding gaps and redraft requests

- LeanExplore did not expose a single Physlib model covering a vertical spring under gravity together with a completely inelastic collision. `ClassicalMechanics.HarmonicOscillator` supplies closely related scalar spring energy, but its available interface does not include the gravity-shifted equilibrium or impact stage. Faithful local law predicates were therefore used.
- No dedicated `DimAcceleration` candidate was returned, so acceleration was assembled from Physlib's dimension algebra.
- The requested `.archon/AGENTS.md` was absent. The current `.archon/PROGRESS.md` and `.archon/prover-modes/physics-formalize.md` were read instead.
- The prompt advertised `archon` on `PATH`, but `archon dag-query` returned `command not found`; no dependency-graph output could be collected. The source report and chapter declare no previous-part dependencies.
- The blueprint chapter exists and is marked `% archon:physics`, but its proof environment contains only the procedural autoformalization instruction rather than the physical derivation. A later blueprint redraft could record the route `k x₀ = m_f g`, free fall, sticking momentum conservation, and post-impact energy conservation.

## Source/law/answer audit

- Source-only information is confined to `MatchesProblemAndFigureReadouts`,
  the qualitative figure vocabulary, the four displayed distances, and
  `recordedDatasetAnswer`. Direct inspection of `phyx_data/test_image/765.png`
  confirmed the fixed support, vertical spring, suspended frame and bottom
  platform, red putty, vertical height arrow, and `30.0 cm` label.
- Law assumptions state Hooke/static equilibrium, constant-gravity free fall,
  one-dimensional sticking-impact momentum conservation, turning-point
  extension geometry, and post-impact mechanical-energy conservation. None
  states a solved stiffness, impact speed, post-impact speed, quadratic root,
  rounded distance, or answer label.
- Answer-side declarations derive the intermediate calibration/speed formulas,
  the quadratic, the exact nonnegative root, nearest-millimetre agreement with
  `0.199 m`, and unique closest choice B. The metadata definition
  `recordedDatasetAnswer` is not a premise and is absent from the theorem type.

## Verification and blueprint marker status

- Fresh iteration-003 `archon-lean-lsp` diagnostics report only six expected `declaration uses sorry` warnings, at the five derived lemmas and the target theorem, with no errors or failed dependencies.
- Fresh iteration-003 `lake env lean PhyXMiniProblems/problem_phyx_mini_0765.lean` exits successfully with the same six warnings.
- `git diff --check` reports no whitespace errors.
- Numerical audit: the exact root is `0.198695497359...`; its distance from `0.199` is `0.000304502641... < 0.0005`, and B is strictly closer than A, C, or D.
- The statement for `thm:physics:phyx_mini_0765:target` is ready for deterministic `\leanok` synchronization. The blueprint was not edited because the task's explicit write-permission section forbids blueprint changes.
