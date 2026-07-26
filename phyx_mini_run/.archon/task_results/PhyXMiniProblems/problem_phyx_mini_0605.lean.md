# Autoformalization result: `problem_phyx_mini_0605.lean`

## Iteration 002 review disposition

- The retry gate's exact reason was missing post-formalization evidence, not a
  defect identified in the Lean statement.  This report now records evidence
  obtained from the completed Lean model, its source report, and the primary
  image.
- Direct inspection of `phyx_data/test_image/605.png` confirms visible ticks
  `10`, `30`, `50`, and `70`, no visible axis text, an absorption-style trace,
  and nearly uniform deep central troughs near horizontal coordinates `42`,
  `46`, and `50`.  The `cm⁻¹` interpretation is a spectroscopic calibration
  inferred from the CO rotational-spectrum scenario; it is not printed in the
  raster.
- The source report records no previous parts and records answer choice C.  The
  latter remains metadata (`recordedDatasetAnswer`) and is not a theorem
  hypothesis.

## Assumption/target split

### Governing laws

- `SatisfiesTwoBodyCenterOfMassGeometry` states that the two center-of-mass lever arms span the interatomic distance and satisfy the two-body mass-balance equation.
- `SatisfiesCarbonMonoxideRigidRotorLaws` states the point-mass moment of inertia, reduced-mass relation, rigid-rotor energy spectrum, Planck transition law, consecutive-line association, frequency/wavenumber calibration, and the observational meaning of the independent adjacent-line separation.
- `HasPhysicalCarbonMonoxideParameters` selects the positive, nondegenerate physical branch without fixing either requested numerical result.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesCarbonMonoxideRotorScenario` records the `¹²C`/`¹⁶O` sites, massless rigid rod, fixed center of mass, and three-dimensional rotational freedom.
- `MatchesPrimaryCarbonMonoxideSpectrum` records the horizontal ticks `10`, `30`, `50`, and `70`, absent axis text labels, the relative-intensity trace with visible absorption minima, and three consecutive central trough readouts at approximately `42`, `46`, and `50 cm⁻¹`.
- `UsesCarbonMonoxideReferenceData` records one atomic mass unit in kilograms, the looked-up `¹²C` and `¹⁶O` isotope masses, Physlib's reduced Planck constant, and Physlib's speed of light.

### Current target conclusions

- `AgreesWithFigureFrequencySeparation setup`: the adjacent line separation is within `10⁹ Hz` of `1.20 × 10¹¹ Hz`.
- `AgreesWithDisplayedBondLength setup .C`: the interatomic distance is within `5 × 10⁻¹² m` of choice C, `1.1 × 10⁻¹⁰ m`.
- `IsUniqueClosestBondLengthChoice setup .C`: choice C is strictly closer than A, B, or D.

## Goal-faithfulness audit

- `adjacentLineFrequencySeparation` and `interatomicDistance` are independent fields of `CarbonMonoxideRotorSetup`; neither is defined from a formula, answer choice, or recorded dataset answer.
- No assumption states a numeric hertz separation or a numeric bond length. The figure premise supplies only calibrated wavenumber positions. Their `4 cm⁻¹` difference is derived in `representativeWavenumberSpacing_eq_four`.
- The governing laws are generic equations for a two-body rigid rotor and spectrometer. They relate independent quantities but contain neither `1.20 × 10¹¹ Hz` nor `1.1 × 10⁻¹⁰ m`.
- The isotope masses and physical constants are reference data, not conclusions about this molecule's bond length.
- `AnswerChoice.bondLengthMeters` is only the displayed alternative table, and `recordedDatasetAnswer` is never a theorem premise.
- The agreement predicates merely state the requested numerical precision. Unfolding them leaves substantive inequalities that require the figure calibration, constants, and rigid-rotor calculation; they do not prove the theorem definitionally.

## Declarations created and blueprint mapping

- Dimensionful roles and readouts: `LengthQuantity`, `MassQuantity`, `MomentOfInertiaQuantity`, `ActionQuantity`, `FrequencyQuantity`, `WavenumberQuantity`, `SpeedQuantity`, and their named-unit readout functions.
- Molecular/figure vocabulary: `AtomSite`, `IsotopeLabel`, `BondModel`, `RotationCenter`, `RotationFreedom`, `FigureAxis`, `SpectrumAxisQuantity`, `SpectrumAxisUnit`, `HorizontalTick`, `RepresentativeSpectrumLine`, and `CarbonMonoxideSpectrumFigure`.
- Independent setup: `CarbonMonoxideRotorSetup`.
- Assumption interfaces: `MatchesCarbonMonoxideRotorScenario`, `MatchesPrimaryCarbonMonoxideSpectrum`, `UsesCarbonMonoxideReferenceData`, `HasPhysicalCarbonMonoxideParameters`, `SatisfiesTwoBodyCenterOfMassGeometry`, and `SatisfiesCarbonMonoxideRigidRotorLaws`.
- Derived lemmas: `representativeWavenumberSpacing_eq_four`, `momentOfInertia_eq_reducedMass_mul_bondLength_sq`, and `adjacentFrequencySeparation_agrees_with_figure`.
- Answer semantics: `AgreesWithFigureFrequencySeparation`, `AnswerChoice`, `AnswerChoice.bondLengthMeters`, `recordedDatasetAnswer`, `answerChoiceErrorMeters`, `AgreesWithDisplayedBondLength`, and `IsUniqueClosestBondLengthChoice`.
- Blueprint label `thm:physics:phyx_mini_0605:target` corresponds to `carbonMonoxideSpectrum_determines_frequencySeparation_and_choiceC`.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `unit-aware physical quantity mass length time frequency energy Planck constant speed of light`: selected `Dimension`, `Constants.ℏ`, `DimSpeed.speedOfLight`, `UnitChoices`, and `UnitChoices.SI`.
- `rigid rotor moment of inertia rotational energy spectrum adjacent transition lines`: inspected the returned classical rigid-body candidates, especially `RigidBody.rotationalKineticEnergy`; these do not provide the quantum spectrum needed here.
- `reduced mass two particles m₁ m₂ product divided by sum`: no applicable two-body reduced-mass declaration was returned.
- `PhysLean Units SI Mass Length Frequency`, `Dimension Frequency inverse time`, `Quantity physical dimension unit choices value`, `Dimensional quantity ℝ Dimension`, `UnitChoices.dimScale`, and `WithDim physical dimension tagged real constructor val`: selected the `Dimensionful (WithDim d M)` representation and the SI/readout interface.
- Exact-name followups `DimEnergy`, `Dimensionful`, `LengthUnit.centimeters`, `MassUnit.kilograms`, `Dimension.L𝓭`, `Dimension.M𝓭`, and `Dimension.T𝓭` verified the declarations and their defining modules before final compilation.
- Iteration-002 source/module fetches revalidated the exact selected entries:
  `Dimensionful` (id 394284, `Physlib.Units.Basic`), `WithDim` (id 394425,
  `Physlib.Units.WithDim.Basic`), `DimEnergy` (id 394468,
  `Physlib.Units.WithDim.Energy`), `Dimension` (id 394292,
  `Physlib.Units.Dimension`), `Constants.ℏ` (id 390795,
  `Physlib.QuantumMechanics.PlanckConstant`), `DimSpeed.speedOfLight` (id
  394486, `Physlib.Units.WithDim.Speed`), `UnitChoices.SI` (id 394270,
  `Physlib.Units.Basic`), and `LengthUnit.centimeters` (id 393160,
  `Physlib.SpaceAndTime.Space.LengthUnit`).

## Physlib/Mathlib names grounded

- `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭` from `Physlib.Units.Dimension`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Dimensionful`, `UnitChoices`, and `UnitChoices.SI` from `Physlib.Units.Basic`.
- `LengthUnit.centimeters` from `Physlib.SpaceAndTime.Space.LengthUnit`.
- `MassUnit.kilograms` from `Physlib.ClassicalMechanics.Mass.MassUnit` (also used by `UnitChoices.SI`).
- `DimEnergy` from `Physlib.Units.WithDim.Energy`.
- `Constants.ℏ` from `Physlib.QuantumMechanics.PlanckConstant`.
- `DimSpeed.speedOfLight` from `Physlib.Units.WithDim.Speed`.
- Mathlib real arithmetic, `Real.pi`, `NNReal`, finite inductive types, scientific-number notation, and absolute value.

## Local abstractions introduced

- The molecular setup and categorical scenario types preserve the two isotope sites, rigid massless rod, fixed center of mass, and three-dimensional rotation rather than replacing these physical roles by untyped scalars.
- `MomentOfInertiaQuantity`, `ActionQuantity`, `FrequencyQuantity`, and `WavenumberQuantity` use Physlib dimensions. Real numbers are exposed only through explicitly named readouts.
- `SatisfiesTwoBodyCenterOfMassGeometry` and `SatisfiesCarbonMonoxideRigidRotorLaws` are local law interfaces because no matching quantum rigid-rotor/reduced-mass API was found. They state standard physical laws without specializing the requested answers.
- `CarbonMonoxideSpectrumFigure` separates the physical wavenumber of each trough from scalar raster metadata.

## Grounding gaps and redraft requests

- LeanExplore exposed classical rigid-body kinetic-energy and inertia-tensor declarations but no matching quantum diatomic rigid-rotor spectrum, spectroscopic line-spacing theorem, or two-particle reduced-mass API. Faithful local predicates were therefore required.
- The source raster has tick values but no visible axis-unit text. The formalization uses the spectroscopic interpretation consistent with the CO rotational-spectrum context and the recorded bond-length choice: the horizontal coordinate is wavenumber in `cm⁻¹`.
- The requested `.archon/AGENTS.md` file was absent. The checked-in `.archon/prover-modes/physics-formalize.md` supplied the matching role discipline.
- The `archon` executable was not available on `PATH`, so the read-only dependency-graph query could not be run. The blueprint contains no declared dependencies beyond its target environment.
- The blueprint environment was not edited to add `\leanok` because this task's explicit write permissions allow edits only to the assigned Lean file and this result file. A blueprint-owning coordinator should mark `thm:physics:phyx_mini_0605:target` with `\leanok`.
- No blueprint content redraft is otherwise needed.

## Verification

- Iteration-002 `archon-lean-lsp` diagnostics: success; four expected
  `declaration uses sorry` warnings at the three derived lemmas and the target
  theorem, with no errors or failed dependencies.
- Iteration-002 `lake env lean PhyXMiniProblems/problem_phyx_mini_0605.lean`:
  exit code 0; the same four expected warnings.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0605.lean`: clean.
