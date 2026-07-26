# Autoformalization result: `problem_phyx_mini_0415.lean`

## Assumption/target split

### Governing laws

- `SatisfiesMonatomicIdealGasProcessLaws.idealGasLawAt` states `pV = nRT` at every labelled equilibrium state.
- `SatisfiesMonatomicIdealGasProcessLaws.monatomicInternalEnergyAt` states the helium caloric equation `U = (3/2)pV` at every state.
- `isothermalEndpointTemperatures` states equal endpoint temperatures for every path classified as isothermal.
- `adiabaticPressureVolumeRatio` states the general ideal-gas relation
  `p_finish / p_start = (V_start / V_finish)^γ` for every adiabatic path, using `Real.rpow` on positive SI volume readouts.
- `isochoricEndpointVolumes` and `isochoricBoundaryWork` state equal endpoint volumes and zero work for any isochoric path.
- `adiabaticHeatExchange` states zero heat exchange for any adiabatic path.
- `firstLaw` states `Q = U_finish - U_start + W` for every directed path, with heat into the gas and work by the gas positive.
- `UsesTextbookHeliumCalibrations` supplies the non-target material calibrations: monatomic ideal-helium model, `4 g/mol`, `R = 8.31 J mol⁻¹ K⁻¹`, `γ = 5/3`, and the mass/amount relation.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records the `120 mg` helium sample.
- It records the axis roles, literal symbols `p` and `V`, displayed units `atm` and `cm³`, and maximum labelled ticks `3 atm` and `3000 cm³`.
- It records the physical state readouts `p₁ = 3 atm`, `V₁ = 1000 cm³`, and `V₂ = V₃ = 3000 cm³`. No numerical pressure is assumed for state `2` or state `3`.
- It records all three state labels and the image-primary arrow cycle `1 → 2 → 3 → 1`.
- It records the upper curved `1 → 2` leg labelled “Isotherm”, the unlabelled vertical `2 → 3` leg, and the lower curved `3 → 1` leg labelled “Adiabat”.
- The answer table is represented by `AnswerChoice.heatInJoules`; `recordedAnswerChoice = C` is dataset metadata, not a law about the physical heat observable.

### Current target conclusions

- `state2PressureInAtmospheres_eq_one` derives the intermediate value `p₂ = 1 atm` from the isothermal law.
- `state3PressureInAtmospheres_eq_rpow` derives `p₃ = (1/3)^(2/3) atm` from the adiabatic reference path.
- `heatTwoToThreeInJoules_exact` derives
  `(3/2)(303975/1000)((1/3)^(2/3) - 1) J` for the signed heat into the gas on `2 → 3`.
- `problem_phyx_mini_0415` repeats that exact physical result and concludes that recorded answer C (`-239 J`) is the unique closest listed choice.

## Goal-faithfulness audit

The requested heat is an independent `EnergyQuantity` field `setup.heatIntoGas .twoToThree`. It is not defined from the answer table, a numerical constant, state energy, or work. None of `HeliumPVProcessSetup`, `MatchesProblemAndPrimaryFigure`, `UsesTextbookHeliumCalibrations`, `HasPhysicalThermodynamicParameters`, or `SatisfiesMonatomicIdealGasProcessLaws` assigns its value.

The law interface is quantified over all states or all paths and contains only standard physical relations. In particular, zero heat is assumed only for a path already classified as adiabatic, which is the distinct `3 → 1` reference leg; no heat conclusion is assumed for the isochoric `2 → 3` target leg. The source answer table necessarily contains the displayed number `-239`, but the substantive theorem does not equate the physical heat to that data by unfolding. It proves an exact model expression and asks separately that C be the unique closest finite choice.

## Declarations created and blueprint correspondence

- Dimensionful layer: `VolumeQuantity`, `PressureQuantity`, `TemperatureQuantity`, `MassQuantity`, `EnergyQuantity`, `MolarGasConstantQuantity`, and named-unit readouts.
- Physical vocabulary: `GasSpecies`, `GasModel`, `GasSample`, `StateLabel`, `ProcessPath`, `ProcessKind`, and `ThermodynamicState`.
- Figure vocabulary: `FigureAxis`, `AxisQuantity`, `AxisDisplayUnit`, `AxisSymbol`, `FigurePathGeometry`, `FigurePathText`, and `PressureVolumeFigure`.
- Setup and premise split: `HeliumPVProcessSetup`, `MatchesProblemAndPrimaryFigure`, `UsesTextbookHeliumCalibrations`, `HasPhysicalThermodynamicParameters`, and `SatisfiesMonatomicIdealGasProcessLaws`.
- Supporting conclusions: `state2PressureInAtmospheres_eq_one`, `state3PressureInAtmospheres_eq_rpow`, and `heatTwoToThreeInJoules_exact`.
- Multiple-choice layer: `AnswerChoice`, `AnswerChoice.heatInJoules`, `recordedAnswerChoice`, and `IsUniqueClosestHeatChoice`.
- Main declaration: `problem_phyx_mini_0415`, corresponding to blueprint label `thm:physics:phyx_mini_0415:target`.

The theorem environment is ready for `\lean{PhyXMiniProblems.ProblemPhyXMini0415.problem_phyx_mini_0415}` and the statement-level `\leanok` marker. The blueprint was not edited because the task's final write-permission block permits changes only to the assigned Lean file and this task-result file; the checked-in role guidance also assigns `\leanok` synchronization to the loop.

## LeanExplore queries/candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- `thermodynamic adiabatic ideal gas pressure volume heat transfer first law`: found `IdealGas.ideal_gas_law`, `DimPressure`, `adiabatic_relation_log`, and related declarations.
- `DimPressure DimEnergy Dimensionful pressure energy units`: found `DimPressure` and `Dimensionful`.
- `DimEnergy`: found `DimEnergy` and `DimEnergy.joule`.
- `real power adiabatic exponent five thirds Real.rpow`: found and used `Real.rpow`; it also found `adiabatic_relation_UaUbVaVb`.
- `ideal monatomic gas internal energy three halves pressure volume`: found the statistical-mechanics `IdealGas` API and `MicroHamiltonian.internalU`, but no direct macroscopic dimensionful caloric-law declaration.
- `DimMass mass units`: did not find a `DimMass` alias suitable for the sample, so mass was represented directly as `Dimensionful (WithDim M𝓭 NNReal)`.
- `Dimensional temperature WithDim Θ` and `Physlib Temperature absolute temperature thermodynamics`: found `Temperature`, but its source says it wraps an arbitrary-unit `NNReal`; a temperature-dimension-tagged `Dimensionful` quantity better preserves the unit role used with the SI ideal-gas law here.

Source and module details were fetched for `IdealGas.ideal_gas_law`, `adiabatic_relation_log`, `adiabatic_relation_UaUbVaVb`, `DimPressure`, `DimEnergy`, `Dimensionful`, `Real.rpow`, and `Temperature` before choosing the final API.

## PhysLean/Mathlib names grounded

- `DimPressure` and `DimPressure.pascal` from `Physlib.Units.WithDim.Pressure`.
- `DimEnergy` and `DimEnergy.joule` from `Physlib.Units.WithDim.Energy`.
- `Dimensionful`, `WithDim`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.Θ𝓭`, and `UnitChoices.SI` from Physlib's unit infrastructure.
- `NNReal` for intrinsically nonnegative mass, volume, temperature, and gas-constant representations.
- `Real.rpow` from `Mathlib.Analysis.SpecialFunctions.Pow.Real` for the dimensionless adiabatic volume ratio.
- Real absolute-value notation for finite answer-choice distance.

## Local abstractions introduced

- `GasSample` preserves species, material model, dimensionful mass, amount-of-substance readout, and molar-mass readout as distinct physical roles; it is not a scalar wrapper.
- `ThermodynamicState` and `HeliumPVProcessSetup` keep state observables and path heat/work independent until the governing laws relate them.
- `PressureVolumeFigure` preserves figure axes, units, labels, geometry, arrows, and schematic ordering separately from the physical states.
- `SatisfiesMonatomicIdealGasProcessLaws` is local because the closest Physlib ideal-gas theorem is unitless (`R = 1`) and the closest adiabatic lemmas use entropy relations among raw real variables rather than a unit-aware macroscopic pressure-volume process. The local interface states standard laws directly and is fully quantified.
- `IsUniqueClosestHeatChoice` is local because no suitable finite-choice nearest-value declaration was found. It directly compares absolute errors and contains no preferred answer internally.

## Grounding gaps and redraft requests

- `IdealGas.ideal_gas_law` in `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` is explicitly unitless and fixes `R = 1`; it is not signature-compatible with this dimensional molar setup.
- `adiabatic_relation_log` and `adiabatic_relation_UaUbVaVb` in `Physlib.Thermodynamics.IdealGas.Basic` are useful entropy-based raw-real results, but do not directly state the pressure-volume ratio law needed here.
- The exact ideal-monatomic-gas value from the visible coordinates and exact SI atmosphere conversion is approximately `-236.8 J`, not exactly `-239 J` and not its nearest-whole-joule rounding. The formalization therefore treats C as the unique closest supplied choice. The blueprint should be fleshed out to state this approximation/choice interpretation or explain the source's numerical convention.
- The blueprint proof currently contains only the generic autoformalization instruction, not the promised informal thermodynamic derivation. A future plan pass should add the `p₂`, `p₃`, and first-law calculation summarized above.
- The requested `.archon/AGENTS.md` and advertised `archon` executable were absent. The checked-in `.archon/prover-modes/physics-formalize.md`, the injected role instructions, and `.archon/PROGRESS.md` were used; DAG navigation could not be performed.
- The assigned Lean file did not exist before this task, so there were no file-specific `/- USER: ... -/` comments to apply.

## Verification

- Lean LSP diagnostics reported only four expected `declaration uses 'sorry'` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0415.lean` exited successfully with those same four warnings.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0415.lean` exited successfully.
