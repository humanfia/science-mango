# Autoformalization result: `problem_phyx_mini_0481.lean`

## Retry gate resolution

The iteration-001 gate reason was that no genuine post-formalization task
result existed.  This report was refreshed after auditing the completed Lean
model against the source JSON, the primary bitmap, and the blueprint; rerunning
the searches listed below; and compiling the assigned file.  No semantic
redraft of the Lean declarations was needed.

## Assumption/target split

### Governing laws

- The working gas obeys the ideal-gas equation of state at all four labelled equilibrium states.
- Monatomic helium has adiabatic index `γ = 5/3` and constant-pressure molar heat capacity `Cₚ = (5/2)R`.
- The compressor leg `4 → 3` and expander leg `2 → 1` obey the isentropic temperature--pressure relation with exponent `(γ - 1) / γ` and transfer no heat.
- The high-pressure leg `3 → 2` and low-pressure leg `1 → 4` are isobaric.
- Compressor input work and expander output work obey the steady-flow enthalpy laws `n Cₚ ΔT`.
- The `Q_H` and `Q_C` magnitudes obey the corresponding isobaric `n Cₚ ΔT` laws with explicit signs for heat transferred to the gas.
- Net work input is compressor input minus expander output and also equals rejected heat minus absorbed heat over a complete cycle.
- Average input power equals net work input per cycle times the cycle frequency.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- The primary image has pressure on the vertical axis in kPa and volume on the horizontal axis in cm³.
- The physically directed reversed cycle is `4 → 3 → 2 → 1 → 4`; the image explicitly draws curved arrows `4 → 3` and `2 → 1` and no horizontal cycle arrowheads.
- States 1 and 4 lie at `150 kPa`; states 2 and 3 lie at `750 kPa`.
- State 4 is the pre-compression state at `100 cm³`; state 1 is the post-expansion state at `80 cm³`.
- The state-4 annotation reads `-23 °C = 250 K`. The physical state is calibrated to `250 K`; the prose's whole-degree Celsius value is modeled by a rounding inequality because `250 K` is exactly `-23.15 °C` under the affine conversion.
- The stated pressure ratio is `5`, and the operating rate is `60 cycles/s`.
- `Q_H` is attached to the upper isobar and directed out of the working gas; `Q_C` is attached to the lower isobar and directed into it.

### Current target conclusions

- The independent input-power observable has exact watt readout
  `450 * (Real.rpow 5 (2 / 5) - 1)`.
- This value rounds to `410 W` and is uniquely closest to displayed answer choice C among `390`, `400`, `410`, and `420 W`.

## Goal-faithfulness audit

The `410 W` result, the exact closed form, the rounding predicate, and the unique-choice conclusion occur only in the derived-answer section and the final theorem. `ReversedBraytonRefrigerator.powerInput` is an independent physical field. No scenario, data, figure, positivity, or governing-law field fixes it to `410 W` or to the derived closed form. The only premise involving power is the general physical law `P = frequency × net work per cycle`, plus positivity.

The answer-choice table and `recordedAnswerChoice := .C` are metadata definitions and are not theorem premises. Unfolding either does not prove the target. Likewise, `exactPowerInputWatts` names a derived scalar expression; it does not define the physical power observable.

The model uses steady-flow enthalpy work `n Cₚ ΔT`, which is the appropriate Brayton compressor/turbine law and is necessary for the recorded approximately `410 W` answer. It does not substitute the closed-system P--V boundary-work formula.

## Declarations created and blueprint correspondence

- Dimensionful quantity interfaces and readouts: `VolumeQuantity`,
  `FrequencyQuantity`, `powerDimension`, `PowerQuantity`, `MolarMeasurement`,
  `pressureInPascals`, `pressureInKilopascals`, `volumeInCubicMeters`,
  `volumeInCubicCentimeters`, `energyInJoules`, `frequencyInHertz`,
  `powerInWatts`, `temperatureInKelvins`, and
  `temperatureInDegreesCelsius`.
- Physical and cycle vocabulary: `WorkingSubstance`, `GasModel`,
  `MolecularType`, `DeviceRole`, `CycleModel`, `StateLabel`, `CycleLeg`,
  `CycleLeg.initialState`, `CycleLeg.finalState`, `ProcessKind`,
  `ThermodynamicState`, `GasSample`, `GasSample.amountInMoles`, and
  `ReversedBraytonRefrigerator`.
- Primary-image vocabulary: `AxisQuantity`, `FigureAxis`, `AxisUnit`,
  `SegmentShape`, `HeatLabel`, `HeatTransferDirection`, `ArrowOrientation`,
  `PressureVolumeDiagram`, and `MatchesPrimaryPressureVolumeFigure`.
- Assumption interfaces: `MatchesReversedBraytonHeliumScenario`,
  `pressureRatio`, `MatchesProblemReadouts`,
  `HasPhysicalRefrigeratorParameters`, and
  `SatisfiesIdealReversedBraytonLaws`.
- Derived stubs: `stateOneTemperatureInKelvins_eq_200`,
  `isentropicEndpointTemperatures`, and `netWorkInputPerCycle_exact`.
- Displayed-answer vocabulary: `exactPowerInputWatts`, `AnswerChoice`,
  `AnswerChoice.displayedPowerWatts`, `recordedAnswerChoice`,
  `RoundsToDisplayedTenWatts`, and `IsUniqueClosestDisplayedPower`.
- Blueprint target `thm:physics:phyx_mini_0481:target`: `reversedBraytonRefrigerator_powerInput_eq_recordedAnswerC`.

The blueprint currently contains only the target environment.  The helper
names above are therefore reported explicitly so the plan/orchestration stage
can add any desired helper environments after accepting the signatures.

## LeanExplore queries and candidates actually used

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `thermodynamics ideal gas law pressure volume temperature amount of substance`
- `adiabatic ideal gas isentropic temperature pressure relation Brayton cycle`
- `Dimensionful WithDim pressure energy power frequency SI units`
- `Temperature TemperatureUnit kelvin absolute temperature`
- `WithDim`
- `DimEnergy.joule`
- `Real.rpow real exponentiation`
- `reversed Brayton refrigeration cycle steady flow compressor turbine enthalpy work`
- `DimVolume DimPower DimFrequency watt hertz cubic meter`

The relevant search candidates were `IdealGas.ideal_gas_law`,
`adiabatic_relation_log`, `adiabatic_relation_UaUbVaVb`, `Temperature`,
`Temperature.toReal`, `TemperatureUnit`, `TemperatureUnit.kelvin`,
`DimPressure`, `DimPressure.pascal`, `DimEnergy`, `DimEnergy.joule`,
`Dimensionful`, `WithDim`, `UnitChoices.SI`, and `Real.instPow` (whose source
installs `Real.rpow`).  Module paths and source were fetched for the candidates
actually used in the file.  The Brayton/steady-flow query returned only
unrelated combinatorial-cycle and dynamical-flow declarations, confirming the
need for a local law interface.

## Physlib/Mathlib names grounded

- `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic`.
- `TemperatureUnit` and `TemperatureUnit.kelvin` from `Physlib.Thermodynamics.Temperature.TemperatureUnits`.
- `DimPressure` and `DimPressure.pascal` from `Physlib.Units.WithDim.Pressure`.
- `DimEnergy` and `DimEnergy.joule` from `Physlib.Units.WithDim.Energy`.
- `Dimension`, `Dimensionful`, `WithDim`, the base-dimension symbols, and `UnitChoices.SI` from Physlib's unit infrastructure.
- `Real.rpow` from `Mathlib.Analysis.SpecialFunctions.Pow.Real`.

LeanExplore source confirmed the dimensional type expressions, SI projections,
absolute-temperature representation, and real-power operation.  The
`archon-lean-lsp` diagnostic pass then accepted the complete file with only the
four intended `sorry` warnings.

## Local abstractions introduced

- Physlib has no specialized volume, frequency, or power aliases in the searched API, so these use its generic `Dimensionful (WithDim ... NNReal)` construction with dimensions `L³`, `T⁻¹`, and `M L² T⁻³` respectively. These preserve the physical dimensions and expose only explicitly named unit readouts.
- Physlib's unit basis has no amount-of-substance dimension. `MolarMeasurement` therefore keeps the amount carrier abstract and exposes a calibrated mole readout, rather than identifying amount of substance with `ℝ`.
- No reversed-Brayton cycle API or steady-flow compressor/turbine law was found. `SatisfiesIdealReversedBraytonLaws` is a local governing-law interface that states the ideal-gas, isentropic, isobaric heat, enthalpy-work, cycle-balance, and average-power relations directly.
- The pressure-volume figure is represented separately from the physical setup so qualitative raster geometry and quantitative state readouts are not hidden in definitions.

## Grounding gaps and redraft requests

- `IdealGas.ideal_gas_law` is a unitsless statistical-mechanics result with `R = 1` for a specific `IdealGas.pressure`; it is not signature-compatible with the dimensionful four-state setup. The local equation-of-state law is therefore used instead.
- `adiabatic_relation_log` and `adiabatic_relation_UaUbVaVb` concern equality of an entropy formula expressed through internal energies and volumes. They do not directly provide the Brayton temperature--pressure law, so the latter is stated faithfully as a local governing law.
- No specialized Physlib API was found for Brayton cycles, steady-flow enthalpy work, power, volume, frequency, or amount of substance.
- The requested `archon dag-query` navigation could not run because `archon` was not on `PATH` in this environment.
- `.archon/AGENTS.md` is absent in this checkout.  The active
  `.archon/prover-modes/physics-formalize.md`, the matching progress entry, the
  exact review-gate reason, source report, blueprint, primary image, and the
  file-specific `/- USER: ... -/` hint were used.  As that hint records, the
  assigned Lean file was absent when the original autoformalization began; it
  was present for this retry audit.
- The blueprint theorem environment was not marked `\leanok` because the task's write-permission section explicitly forbids editing blueprint chapters. The plan/orchestration stage should add `\leanok` for `thm:physics:phyx_mini_0481:target` after accepting this formalization.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0481.lean` exits successfully with only the four expected `declaration uses sorry` warnings, for the three derived lemmas and the final blueprint theorem.
