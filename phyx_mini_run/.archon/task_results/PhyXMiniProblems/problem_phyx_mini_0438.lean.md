## Assumption/target split

### Governing laws

- `SatisfiesIdealDieselCycleLaws` contains the macroscopic ideal-gas equation at each numbered state, Mayer's relation, `γ = Cₚ/Cᵥ`, ideal-air internal energy, `T V^(γ-1)` conservation and zero heat on adiabatic legs, constant-pressure and constant-volume process relations, their heat/work formulas, and the first law on every leg.
- `ModelsConstantPressureFuelInjection` connects the stated combustion energy to heat entering the air on the `2 → 3` ignition leg.
- `SatisfiesEngineTimingAndPowerLaw` gives the crankshaft/cycle-frequency conversion and the general engine law `P = N f W_cycle`. Its one-cycle-per-revolution convention is explicit because that convention is needed to reproduce the recorded option.
- `HasPhysicalDieselParameters` contains positivity and nondegeneracy conditions only.

### Previous-part results

- None. The source report's `previous_parts` array is empty. No temperature, cutoff ratio, net work, efficiency, or power result is assumed.

### Figure/data readouts

- `MatchesProblemStatement` records ideal intake air, displacement `1000 cm³`, compression ratio `21`, `γ = 1.40`, intake temperature `25 °C`, intake pressure one standard atmosphere, `1000 J` combustion heat per cylinder cycle, eight cylinders, and `2400 rpm`.
- The same structure connects displacement to `V₁ - V₂` and the compression ratio to `V₁/V₂`, preserving the two defining equations in the source instead of leaving the named parameters detached from the numbered states.
- `MatchesPrimaryPVDiagram` records the pressure/volume axes and displayed units, all printed labels, plotted-state agreement, `V₁ = 1050 cm³`, `V₂ = 50 cm³`, `V₄ = V₁`, the interior position of `V₃`, `p₁ = 1 atm`, and `p₂ = p₃ = p_max`.
- Direct inspection of `438.png` gives adiabatic `1 → 2`, constant-pressure ignition `2 → 3`, adiabatic `3 → 4`, and constant-volume exhaust `4 → 1`. Black cycle-direction arrowheads are visible only on the two curved adiabats; the large purple `Q_H` and `Q_C` arrows are heat-transfer annotations, not cycle-direction arrows. The auxiliary generated caption is not used where it contradicts the bitmap.

### Current target conclusions

- `dieselEnginePowerOutputIsAnswerD` concludes that the independently modeled dimensionful output power, read in kilowatts, is strictly nearest to displayed choice D (`211 kW`).
- The net cycle work, numerical output power, and selected answer do not occur as hypotheses or fields of any premise structure.

## Goal-faithfulness audit

- `DieselEngineCycle.outputPower` is an independent dimensionful observable. It is constrained only by the general engine power law and is not defined from `211`, `.D`, or `recordedAnswerChoice`.
- `netCycleWorkInJoules` is the sum of the four signed process works. It is not a hard-coded intermediate result.
- `SatisfiesIdealDieselCycleLaws`, `ModelsConstantPressureFuelInjection`, and `SatisfiesEngineTimingAndPowerLaw` state governing physical relations, not the current answer. None contains a numerical work or power conclusion.
- The measured `1000 J` is source data for combustion heat and is connected only to heat input on `2 → 3`.
- `recordedAnswerChoice` is isolated dataset metadata and is not a theorem premise. `displayedPowerInKilowatts` merely transcribes all four printed choices; the substantive conclusion remains strict nearest-choice comparison against every other option.
- The added displacement/compression equations and corrected arrow visibility are source/model constraints independent of the target power. They do not make the theorem true by unfolding.

## Declarations created and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0438:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0438.dieselEnginePowerOutputIsAnswerD`.
- Dimensionful quantities and readouts: `VolumeQuantity`, `HeatCapacityQuantity`, `MolarGasConstantQuantity`, `FrequencyQuantity`, `PowerQuantity`, and the named SI/display-unit readout functions.
- Figure/model vocabulary: `CycleState`, `CycleLeg`, `ProcessKind`, `AxisQuantity`, `AxisDisplayUnit`, `DiagramLabel`, `ThermodynamicState`, `DieselPVDiagram`, `GasModel`, `GasSample`, and `DieselEngineCycle`.
- Premise interfaces: `MatchesProblemStatement`, `MatchesPrimaryPVDiagram`, `HasPhysicalDieselParameters`, `SatisfiesIdealDieselCycleLaws`, `ModelsConstantPressureFuelInjection`, and `SatisfiesEngineTimingAndPowerLaw`.
- Derived/answer vocabulary: `netCycleWorkInJoules`, `AnswerChoice`, `displayedPowerInKilowatts`, `recordedAnswerChoice`, and `IsNearestDisplayedPowerChoice`.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `physical dimensions units pressure volume temperature energy power` returned `DimPressure`, `DimEnergy`, `Dimension`, and `UnitChoices.dimScale`.
- `thermodynamic ideal gas adiabatic process Diesel cycle` returned `IdealGas.ideal_gas_law`, `adiabatic_relation_log`, and `adiabatic_relation_UaUbVaVb`.
- `DimPressure DimEnergy Temperature UnitChoices.SI` returned `UnitChoices.SI`, `DimPressure.pascal`, `TemperatureUnit`, and `DimPressure`.
- `Dimensionful WithDim scaleUnit physical units` returned `Dimensionful`, `CarriesDimension.toDimensionful`, and related scaling declarations.
- Exact-name queries `DimPressure.standardAtmosphere`, `DimEnergy.joule`, `Temperature TemperatureUnit.kelvin`, `Temperature.toReal`, and `Real.rpow` grounded the corresponding names used in the file.
- `DimVolume DimPower DimFrequency DimHeatCapacity` returned general dimensional infrastructure and `DimEnergy`, but no ready-made declarations with those four requested physical roles.
- `Diesel cycle engine power thermodynamic process` returned general entropy/adiabatic results but no Diesel-cycle or engine-power interface.
- `Finset.sum over a finite type` was checked for the finite cycle-leg sum; no specialized physics declaration was needed beyond Mathlib's standard big-operator notation.
- Source was fetched for `Dimensionful`, `DimPressure`, `DimPressure.pascal`, `DimPressure.standardAtmosphere`, `DimEnergy`, `DimEnergy.joule`, `UnitChoices.SI`, `TemperatureUnit`, `TemperatureUnit.kelvin`, `Temperature.toReal`, `Real.rpow`, `IdealGas.ideal_gas_law`, `adiabatic_relation_log`, and `adiabatic_relation_UaUbVaVb`.
- The packaged ideal-gas theorem is for a units-free statistical-mechanics model with `R = 1`; the packaged adiabatic results require equality of a particular entropy function. They are near misses for this dimensionful, four-state macroscopic cycle and therefore were inspected but not used as premise types.

## Physlib/Mathlib names grounded

- Used directly: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `Dimension.Θ𝓭`, `UnitChoices.SI`, `DimPressure`, `DimPressure.pascal`, `DimPressure.standardAtmosphere`, `DimEnergy`, `DimEnergy.joule`, `Temperature`, `Temperature.toReal`, `TemperatureUnit`, `TemperatureUnit.kelvin`, `NNReal`, `Real.rpow`, and finite big-operator sums over a `Fintype`.
- `DimPressure` and `DimEnergy` are the signed Physlib quantity types appropriate to pressure and process energy/work/heat. Absolute volumes, heat capacities, rates, and output power use nonnegative dimension-tagged carriers.

## Local abstractions introduced

- `VolumeQuantity`, `HeatCapacityQuantity`, `MolarGasConstantQuantity`, `FrequencyQuantity`, and `PowerQuantity` are `Dimensionful (WithDim …)` physical quantity types. They are neither scalar aliases nor one-field scalar wrappers; their tags preserve `L³`, energy/temperature, inverse-time, and energy/time roles.
- Amount of substance is represented by an abstract `AmountOfSubstance` and a named mole readout because the five-coordinate Physlib `Dimension` has no amount-of-substance coordinate.
- `SatisfiesIdealDieselCycleLaws` is the smallest local interface containing the macroscopic laws needed by this problem because the available Physlib thermodynamics theorems use a different, units-free statistical-mechanics state model.
- The strict-nearest-choice target represents the multiple-choice question without falsely requiring the continuous ideal-gas calculation to be exactly equal to the rounded printed integer.

## Grounding gaps and redraft requests

- `.archon/AGENTS.md` is absent in this checkout. The available `.archon/prover-modes/physics-formalize.md` was read and followed.
- The `archon` executable advertised for DAG queries is not on `PATH`; the source report nevertheless confirms that there are no previous-part dependencies.
- LeanExplore exposed no ready-made Physlib volume, heat-capacity, frequency, power, Diesel-cycle, or engine-power declarations suitable for this model. Dimension-correct local quantity types and governing-law interfaces fill those gaps.
- The auxiliary caption reverses/misclassifies parts of the cycle. The formalization follows the primary image, where both curved legs are adiabats and the vertical `4 → 1` leg is exhaust/constant-volume heat rejection.
- The source states `2400 rpm` but does not explicitly state thermodynamic cycles per crank revolution. The recorded `211 kW` option requires one cycle per revolution per cylinder; a conventional four-stroke interpretation would use one cycle per two revolutions and would not select a printed option. The blueprint should make its intended timing convention explicit.
- The blueprint was not edited to add `\leanok` because the task's final write-permission section permits edits only to the assigned Lean file and this task-result file. The plan/orchestration agent should add `\leanok` to `thm:physics:phyx_mini_0438:target` after accepting the formalization.

## Verification

- `archon-lean-lsp` diagnostics report only the expected `declaration uses sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0438.lean` succeeds with the same single expected warning.
