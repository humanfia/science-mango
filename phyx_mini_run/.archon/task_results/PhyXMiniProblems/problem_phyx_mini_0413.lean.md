# Autoformalization result: `problem_phyx_mini_0413.lean`

## Status

- Archon iteration 002 redrafted and revalidated `PhyXMiniProblems/problem_phyx_mini_0413.lean` under the autoformalization retry protocol.
- Confirmed that the blueprint contains `% archon:physics`.
- Addressed the exact review-gate failure (`physics target does not import Mathlib`) by adding a direct `import Mathlib` while retaining the complete dimensionful physics statement.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0413.lean` exits successfully.
- Archon Lean LSP and the command-line compiler both report only the three expected `declaration uses sorry` warnings, for the two intermediate physics lemmas and the main theorem.
- The requested `.archon/AGENTS.md` was absent in this project checkout. The task's supplied `physics-formalize` instructions and `.archon/PROGRESS.md` were followed.
- The `archon` executable advertised for DAG queries was not available on `PATH`; no dependency-graph result could be obtained.

## Extracted physical model

- Working substance: a gas sample identified as hydrogen.
- Amount: `0.015 mol = 15/1000 mol`.
- Initial figure state `i`: `V_i = 100 cm³`, `p_i = 4 atm`.
- Final figure state `f`: `V_f = 300 cm³`, `p_f = 1 atm`.
- Process geometry: a directed straight segment from `i` to `f`, hence an expansion with linearly decreasing pressure.
- Physical state quantities: dimensionful pressure, volume, internal energy, work, and heat; Physlib absolute temperature; dimensionful molar gas constant and constant-volume heat capacity.
- Sign convention: heat is positive into the gas and work is positive when done by the gas, so `Q = U_f - U_i + W_by`.
- Exact standard-atmosphere conversion: `1 atm = 101325 Pa` through `DimPressure.standardAtmosphere`.
- Effective thermal model implicit in the recorded answer: ideal gas with `C_V = (3/2)R`.
- Exact result in this model: `W_by = 4053/80 J`, `ΔU = -12159/800 J`, and `Q = 28371/800 J = 35.46375 J`.
- Multiple-choice conclusion: the displayed `36 J` value, choice C, is uniquely closest to the exact modeled heat.

The primary bitmap was treated as authoritative. It visibly places `f` at `300 cm³`, not the auxiliary caption's approximate `250 cm³`.

## Assumption/target split

### Governing laws

- `SatisfiesStraightPVPathAndWorkLaw`:
  - the parametrized path begins at `i` and ends at `f`;
  - pressure and volume are affine along `t ∈ [0,1]`;
  - quasistatic boundary work on a straight pressure trace is average endpoint pressure times the volume change.
- `SatisfiesIdealGasEnergyAndFirstLaws`:
  - endpoint ideal-gas equations `pV = nRT`;
  - endpoint internal-energy equations `U = n C_V T`;
  - the first-law relation `Q = U_f - U_i + W_by`.
- `UsesThreeDegreeIdealGasCalibration`:
  - `R = 8.314 J mol⁻¹ K⁻¹`;
  - `C_V = (3/2)R`, made explicit because it is the calibration needed by the recorded answer.
- `HasPhysicalProcessParameters` supplies only positivity/domain conditions.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- `MatchesProblemDescription` records hydrogen, the ideal-gas model selection, and `0.015 mol`.
- `MatchesPrimaryFigure` records:
  - horizontal `V` axis in `cm³`, range `0` to `300`;
  - vertical `p` axis in atmospheres, range `0` to `4`;
  - exact points `i = (100,4)` and `f = (300,1)`;
  - visible `i` and `f` labels;
  - the straight segment and arrow from `i` to `f`;
  - equality between scalar plot coordinates and readouts of the dimensionful endpoint states.

### Current target conclusions

- `workDoneByGas_in_joules`: `W_by = 4053/80 J`.
- `internalEnergyChange_in_joules`: `ΔU = -12159/800 J`.
- `problem_phyx_mini_0413`:
  - `Q = 28371/800 J` exactly in the stated model;
  - answer C (`36 J`) is the unique closest displayed choice.

## Goal-faithfulness audit

- `heatTransferredToGas`, `workDoneByGas`, and both endpoint internal energies are independent fields of `HydrogenStraightPVProcess`; none is defined from an answer value.
- No assumption field states `Q = 28371/800`, `Q = 36`, that choice C is correct, or any algebraically equivalent numerical heat conclusion.
- The recorded dataset label is the standalone definition `recordedDatasetAnswer`; it is not used as a premise.
- The straight-line work equation is a general endpoint boundary-work law, not a numerical work or heat premise.
- The ideal-gas, internal-energy, and first-law fields are symbolic physical relations over independently stored quantities.
- `displayedHeatInJoules` only transcribes the answer table. Correctness is a theorem conclusion through `IsUniqueClosestDisplayedHeat`.
- The theorem does not falsely equate the exact SI result with the printed `36 J`; it proves the exact model value and the multiple-choice comparison separately.
- The effective `C_V = (3/2)R` choice is explicit and named, rather than hidden in a local definition or folded into the final heat formula.

## Declarations created and blueprint correspondence

- Dimensionful/readout layer:
  - `VolumeQuantity`
  - `MolarEnergyPerKelvin`
  - `volumeInCubicMeters`
  - `volumeInCubicCentimeters`
  - `pressureInPascals`
  - `pressureInAtmospheres`
  - `energyInJoules`
  - `temperatureInKelvins`
  - `molarEnergyPerKelvinInSI`
- Physical/figure layer:
  - `GasSpecies`, `EquationOfStateModel`, `GasSample`
  - `StateLabel`, `ThermodynamicState`
  - `FigureAxis`, `AxisQuantity`, `AxisDisplayUnit`, `FigurePointLabel`, `PathGeometry`
  - `PressureVolumeDiagram`, `HydrogenStraightPVProcess`
- Assumption interfaces:
  - `MatchesProblemDescription`
  - `MatchesPrimaryFigure`
  - `HasPhysicalProcessParameters`
  - `UsesThreeDegreeIdealGasCalibration`
  - `SatisfiesStraightPVPathAndWorkLaw`
  - `SatisfiesIdealGasEnergyAndFirstLaws`
- Conclusions:
  - `workDoneByGas_in_joules`
  - `internalEnergyChange_in_joules`
  - `problem_phyx_mini_0413`, corresponding to blueprint label `thm:physics:phyx_mini_0413:target`.

The blueprint chapter was not edited to add `\leanok`, because the task's final write-permission block explicitly permits edits only to the assigned Lean file and this task-result file and explicitly forbids blueprint edits.

## LeanExplore queries/candidates actually used

All iteration-002 searches used `packages: ["Mathlib", "Physlib"]`.

- Query: `first law of thermodynamics heat transferred internal energy work`
  - Candidates included `MicroHamiltonian.internalU`, `CanonicalEnsemble.heatCapacity`, `DimEnergy`, and `IdealGas.ideal_gas_law`.
  - No matching macroscopic first-law declaration was returned.
- Query: `ideal gas law pressure volume amount temperature`
  - Candidates included `IdealGas.ideal_gas_law`, `DimPressure`, and `Temperature`.
  - Source inspection showed it is a unitsless statistical-mechanics theorem with `R = 1` and pressure defined from `IdealGas.pressure`; its signature does not model this SI pressure-volume process, so it was not applied directly.
- Query: `work along a straight line pressure volume diagram trapezoid`
  - Candidates included `curveIntegral_segment` and `sum_trapezoidal_integral_adjacent_intervals`.
  - Neither candidate is a thermodynamic `∫p dV` boundary-work law with the required physical quantities.
- Query: `DimPressure standardAtmosphere DimEnergy Temperature Dimensionful WithDim`
  - Candidates included `DimPressure`, `DimPressure.pascal`, `DimEnergy`, and the base-dimension declarations.
- Query: `Dimensionful WithDim UnitChoices.SI`
  - Used `Dimensionful` and `UnitChoices.SI` as the unit-system foundation for local dimensionful quantities and scalar readouts.
- Query: `DimPressure.standardAtmosphere`
  - Used `DimPressure`, `DimPressure.pascal`, and `DimPressure.standardAtmosphere`.
- Query: `DimEnergy.joule`
  - Used `DimEnergy` and `DimEnergy.joule`.
- Query: `Temperature.toReal`
  - Used `Temperature.toReal` for the explicitly named kelvin scalar readout.
- Query: `WithDim`
  - Used `WithDim` to retain the `L³` and energy-per-temperature dimensional roles of local types.
- Query: `DimVolume cubic centimeter`
  - Returned no ready dimensionful volume type; the only unit-related hit was `LengthUnit.centimeters`.
- Query: `amount of substance mole dimension unit`
  - Returned generic `Dimensionful`/`Dimension` infrastructure but no amount-of-substance or mole dimension.

Fetched source/module data for:

- `IdealGas.ideal_gas_law` — `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas`.
- `Dimensionful` and `UnitChoices.SI` — `Physlib.Units.Basic`.
- `WithDim` — `Physlib.Units.WithDim.Basic`.
- `DimPressure` and `DimPressure.pascal` — `Physlib.Units.WithDim.Pressure`.
- `DimPressure.standardAtmosphere` — `Physlib.Units.WithDim.Pressure`.
- `DimEnergy` and `DimEnergy.joule` — `Physlib.Units.WithDim.Energy`.
- `Temperature` and `Temperature.toReal` — `Physlib.Thermodynamics.Temperature.Basic`.

## Physlib/Mathlib names grounded

- `Dimension`, `Dimensionful`, `WithDim`
- `M𝓭`, `L𝓭`, `T𝓭`, `Θ𝓭`
- `UnitChoices.SI`
- `DimPressure`, `DimPressure.pascal`, `DimPressure.standardAtmosphere`
- `DimEnergy`, `DimEnergy.joule`
- `Temperature`, `Temperature.toReal`
- `NNReal`
- `Set.Icc`

## Local abstractions introduced

- `VolumeQuantity`: Physlib has the generic `Dimensionful (WithDim ...)` infrastructure but LeanExplore found no ready `DimVolume`; the local type retains the physical `L³` dimension and a nonnegative carrier.
- `MolarEnergyPerKelvin`: retains energy-per-temperature dimensions while the mole count is an explicit scalar readout, matching the available four-base-dimension unit system.
- `GasSample`: preserves the physical sample, chemical species, equation-of-state role, and mole readout rather than reducing the gas to a scalar.
- `PressureVolumeDiagram` and its enums: preserve axis meanings/units, figure labels, endpoint coordinates, straight geometry, and arrow direction.
- `HydrogenStraightPVProcess`: stores independent dimensionful states, heat, and work.
- The three law/calibration structures: faithfully state the missing macroscopic thermodynamic laws without encoding the requested numerical heat.

## Grounding gaps

- LeanExplore returned no ready Physlib type specialized to volume and no amount-of-substance/mole dimension in the available unit system.
- No matching macroscopic first-law declaration was found.
- No matching thermodynamic straight-path boundary-work theorem was found.
- `IdealGas.ideal_gas_law` is a near miss because it is unitsless (`R = 1`) and tied to a statistical-mechanics pressure definition rather than arbitrary measured endpoint states.
- The auxiliary caption says the final volume is approximately `250 cm³`, while the bitmap clearly shows the final point at `300 cm³`. The formalization follows the instruction to use the image as primary evidence.

## Redraft request

The source should clarify the intended hydrogen model. Ordinary molecular hydrogen near the endpoint temperatures would normally use `C_V = (5/2)R`, which gives approximately `25.33 J`, not `36 J`. The recorded `36 J` value is reproduced only by the effective three-degree relation `C_V = (3/2)R`, giving the exact SI value `35.46375 J`. A future blueprint redraft should either:

1. state that the sample is treated with only three translational quadratic degrees of freedom (or change the gas to a monatomic species), or
2. retain molecular hydrogen and revise the quantitative expected value/model discussion.

Under the present formalization, this ambiguity is exposed as `UsesThreeDegreeIdealGasCalibration` and is not hidden in the answer predicate.
