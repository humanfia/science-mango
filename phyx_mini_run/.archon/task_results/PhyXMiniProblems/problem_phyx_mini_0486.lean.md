# Autoformalization result: `problem_phyx_mini_0486.lean`

## Assumption/target split

### Governing laws

- `ObeysImpactEnergyAndCalorimetryLaws setup` states the general
  translational kinetic-energy loss
  `ΔK = (1/2) m (v_before² - v_after²)` for one blow.
- Its `identicalBlowEnergiesAdd` field adds the losses from the dimensionless
  natural-number blow count.
- Its `nailAbsorbsAllLostEnergy` field is the source assumption that all lost
  hammer energy becomes energy absorbed by the nail.
- Its `constantSpecificHeatCalorimetry` field states the governing sensible
  heating relation `Q = m c ΔT`.
- `HasPhysicalImpactParameters setup` supplies only input positivity and the
  physically relevant speed ordering; it gives no value or interval for the
  temperature rise.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure setup` records the prose values: hammer-head
  mass `1.20 kg`, speed before impact `7.5 m/s`, zero speed after impact, nail
  mass `14 g = 14/1000 kg`, eight blows, and quick succession.
- It also records the iron nail, unspecified metallic hammer head, wooden
  handle and block, the four visible objects, motion toward the nail, the nail
  partly entering the wood, visible wood grain and motion strokes, and the
  absence of numerical figure annotations.
- `UsesRoundedIronSpecificHeat setup` exposes the independently required
  classroom calibration `c_iron = 450 J/(kg K)`. The source does not print a
  material-property table, so this value is not hidden in a helper definition.
- `AnswerChoice` and `displayedTemperatureRiseDegreesCelsius` preserve all
  four printed choices: `28 °C`, `52 °C`, `34 °C`, and `43 °C`.

### Current target conclusions

- `nailTemperatureRise_exact` derives the unrounded model prediction
  `ΔT = 300/7 K` (approximately `42.857 K`).
- `problem_phyx_mini_0486` concludes that the modeled rise rounds to the
  recorded answer D, `43 °C`, and that D is uniquely closest among the four
  displayed choices.

## Goal-faithfulness audit

Neither `300/7`, `43`, nor the correct label D occurs in a problem-data,
material-calibration, physical-validity, or governing-law premise. The setup
stores the temperature rise and energy observables independently; none is
defined from the inputs or the answer table. The only premise involving the
temperature rise is the generic calorimetry law `Q = m c ΔT`, which does not
fix a numerical answer without the independent data and energy-transfer laws.

`recordedAnswerChoice` and the complete answer table encode dataset metadata,
not a proof that D agrees with the physical model. Unfolding
`RoundsToDisplayedWholeDegree` or
`IsUniqueClosestDisplayedTemperatureRise` leaves substantive inequalities
about the independently stored temperature rise. Thus no target conclusion is
smuggled into a structure field, hypothesis, or definitional equality.

The final statement uses a half-degree rounding tolerance rather than falsely
asserting that the exact prediction `300/7` equals `43`. Temperature rise is a
temperature interval, whose numerical size is the same in kelvins and degrees
Celsius; the formalization does not confuse that interval with an absolute
Celsius temperature.

## Declarations created and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0486:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0486.problem_phyx_mini_0486`.
- The derived intermediate declaration is
  `PhyXMiniProblems.ProblemPhyXMini0486.nailTemperatureRise_exact`.
- Dimensionful quantity declarations: `MassQuantity`, `SpeedQuantity`,
  `EnergyQuantity`, `SpecificHeatCapacityQuantity`, and
  `TemperatureDifferenceQuantity`, together with coherent-SI readout
  functions.
- Physical and figure declarations: `FigureObject`, `MaterialKind`,
  `ImpactTiming`, `HammerNailFigure`, and `HammerNailHeatingSetup`.
- Assumption-side declarations: `MatchesProblemAndPrimaryFigure`,
  `UsesRoundedIronSpecificHeat`, `HasPhysicalImpactParameters`, and
  `ObeysImpactEnergyAndCalorimetryLaws`.
- Answer declarations: `AnswerChoice`,
  `displayedTemperatureRiseDegreesCelsius`, `recordedAnswerChoice`,
  `RoundsToDisplayedWholeDegree`, and
  `IsUniqueClosestDisplayedTemperatureRise`.

The blueprint chapter was not edited to add `\leanok`, because the task's
explicit write-permission section limits edits to the assigned Lean file and
this result file. An authorized blueprint synchronization step should add the
marker.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language queries `dimensionful physical mass speed energy SI unit
  readout`, `specific heat capacity calorimetry Q equals mass times specific
  heat times temperature difference`, and `temperature difference dimension
  kelvin Celsius interval` found `Dimensionful` (id 394284),
  `UnitChoices.SI` (394270), `Temperature` (394201),
  `TemperatureUnit.kelvin` (394250), and
  `CanonicalEnsemble.heatCapacity` (393896).
- Likely-name queries `DimEnergy`, `DimSpeed`, `WithDim`, `DimMass`,
  `DimTemperature`, `Temperature`, `TemperatureUnit.kelvin`, and
  `MassUnit.kilogram` grounded `DimEnergy` (394468), `DimEnergy.joule`
  (394469), `DimSpeed` (394481), `WithDim` (394425), and
  `MassUnit.kilograms` (385377). They also confirmed that no `DimMass` or
  `DimTemperature` declaration was returned.
- Dimension-name queries `Dimension.M𝓭`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, and `Dimension.Θ𝓭` grounded the four base dimensions
  actually composed by the local quantity types: ids 394336, 394324, 394330,
  and 394338, respectively.
- The semantic query `specific heat dimension L squared T inverse squared
  temperature inverse` again returned only the unrelated canonical-ensemble
  heat-capacity API and the general dimension machinery, not a dimensionful
  specific-heat-capacity type or the elementary `Q = mcΔT` law.

Source and module data were fetched for every retained Physlib candidate:
`Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, and
`Dimension.Θ𝓭` from `Physlib.Units.Dimension`; `UnitChoices.SI` and
`Dimensionful` from `Physlib.Units.Basic`; `WithDim` from
`Physlib.Units.WithDim.Basic`; `DimSpeed` from
`Physlib.Units.WithDim.Speed`; and `DimEnergy`/`DimEnergy.joule` from
`Physlib.Units.WithDim.Energy`.

For the two near misses, source and module data were also inspected:
`Temperature` from `Physlib.Thermodynamics.Temperature.Basic` is an absolute
temperature wrapper over `NNReal`, not a unit-independent temperature
interval, while `CanonicalEnsemble.heatCapacity` from
`Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` is the derivative of
mean energy for a canonical ensemble, not elementary material-specific heat.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.M𝓭`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `Dimension.Θ𝓭`, `UnitChoices.SI`, `DimSpeed`, `DimEnergy`,
  and `DimEnergy.joule`.
- Mathlib: `NNReal`, real coercions, absolute value, powers, natural-to-real
  coercion, finite inductive types, and real inequalities.

## Local abstractions introduced

- `MassQuantity`, `SpecificHeatCapacityQuantity`, and
  `TemperatureDifferenceQuantity` compose Physlib's genuine
  `Dimensionful (WithDim ...)` infrastructure. They are not scalar aliases and
  retain mass, specific-heat, and temperature dimensions across unit choices.
- `HammerNailHeatingSetup` keeps all independent physical observables,
  including intermediate energies and the requested rise, as distinct
  dimensionful quantities.
- `HammerNailFigure`, `FigureObject`, `MaterialKind`, and `ImpactTiming`
  preserve the image geometry, material roles, and quick-succession condition
  without turning them into unrelated scalar flags.
- `ObeysImpactEnergyAndCalorimetryLaws` is the smallest local law interface
  needed because no matching elementary impact/calorimetry declaration was
  found. Its fields are governing relations, not the answer formula.
- The two displayed-answer predicates formalize whole-degree reporting and
  unique multiple-choice selection without assuming which choice succeeds.

## Grounding gaps and redraft requests

- LeanExplore found no elementary Physlib calorimetry declaration for
  `Q = mcΔT`, no dimensionful specific-heat-capacity alias, and no iron
  material-property table. The formalization therefore composes the public
  dimension machinery and states the calorimetry law locally.
- The source omits the numerical specific heat of iron required for the
  recorded answer. A blueprint redraft should explicitly state the rounded
  classroom calibration `450 J/(kg K)` and the whole-degree rounding
  convention. This formalization exposes both rather than hiding them.
- The requested `.archon/AGENTS.md` is absent from this project. The available
  `.archon/prover-modes/physics-formalize.md`, `PROGRESS.md`, blueprint, source
  report, and primary image supplied the applicable context. The assigned
  file's `/- USER: ... -/` hint reports that the source file did not exist when
  the initial autoformalization began.
- The advertised `archon` executable was not available on `PATH`, so the
  optional read-only DAG query could not be run. The source report independently
  confirms that there are no previous-part dependencies.

## Verification

- `archon-lean-lsp` diagnostics report success with exactly the two expected
  `declaration uses sorry` warnings, for the exact-value lemma and target
  theorem, and no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0486.lean` exits with code
  0 and the same two expected warnings.
