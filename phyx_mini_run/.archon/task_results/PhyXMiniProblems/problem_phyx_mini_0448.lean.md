# PhyXMiniProblems/problem_phyx_mini_0448.lean

## Summary

- Created the previously missing physics-formalization file for the sole blueprint block `thm:physics:phyx_mini_0448:target`.
- Preserved dimensionful pressure, area, length, volume, and absolute temperature; real-valued fields are explicitly mixed-unit readouts, mole readouts, or displayed answer values.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0448.lean` exits successfully with only the expected `declaration uses sorry` warning on the target theorem.

## Assumption/target split

### Governing laws

- `SatisfiesPistonSweepGeometry`: the volume newly swept beneath the piston is its physical cross-sectional area times its upward displacement, expressed as compatible `ft^3`, `ft^2`, and `ft` readouts.
- `SatisfiesIsothermalIdealGasInventory`: separate `p V = n R T` inventory equations hold for the air initially in rigid tank A, the air finally remaining in tank A, and the air admitted into the swept volume beneath the constant-load piston.
- `ConservesAirDuringTransfer`: initial tank moles equal final tank moles plus the moles admitted into cylinder B.
- `HasPhysicalParameters`: pressure, geometry, temperature, gas constant, and gas-inventory readouts have the signs needed to select the physical, nondegenerate branch.

### Previous-part results

- None. The source report lists no previous parts, and no earlier result is assumed.

### Figure/data readouts

- Tank A is rigid, has volume `35 ft^3`, and initially contains air at `225 psia`.
- The piston has area `1 ft^2`, rises slowly upward by `7 ft`, and has a `40 psia` floating-pressure calibration.
- The process is isothermal at `600 R`; the selected absolute unit is Physlib's `TemperatureUnit.absoluteFahrenheit`, i.e. the Rankine degree scale.
- The valve is closed before opening, open during piston motion, and closed afterward; air transfers from tank A to cylinder B.
- Image `448.png` contributes the labelled tank A, cylinder B, piston, valve, downward gravity arrow, connecting passage, gas below the piston, and the tank-left/cylinder-right placement.

### Current target conclusions

- `pressureInPsia setup.tankAFinalPressure = 217`.
- That pressure equals displayed answer D and uniquely selects D among the four displayed pressure values.

## Goal-faithfulness audit

- `RigidTankPistonSetup.tankAFinalPressure` is an independent `DimPressure` field. It is not defined from `217`, from a pressure-balance helper, or from an answer choice.
- Neither `MatchesProblemAndPrimaryFigure`, `HasPhysicalParameters`, `SatisfiesPistonSweepGeometry`, `SatisfiesIsothermalIdealGasInventory`, nor `ConservesAirDuringTransfer` contains `217` or asserts the target final-pressure equality.
- The ideal-gas assumptions state three general physical inventory relations with independently stored mole readouts and a gas-constant readout. Conservation connects those inventories without mentioning the pressure answer.
- `answerPressureInPsia .D = 217` records the supplied multiple-choice display only. It does not constrain the independent final-pressure field; equality with that field occurs solely in the theorem conclusion.
- `recordedAnswerChoice := .D` records dataset metadata and is not used as a premise or as a shortcut to prove the numerical pressure.

## Declarations created and blueprint alignment

- Blueprint label `thm:physics:phyx_mini_0448:target` maps to `PhyXMiniProblems.ProblemPhyXMini0448.finalTankPressure_eq_217_psia`.
- Supporting physical model: `TankPistonFigure`, `RigidTankPistonSetup`, `MatchesProblemAndPrimaryFigure`, `HasPhysicalParameters`, `SatisfiesPistonSweepGeometry`, `SatisfiesIsothermalIdealGasInventory`, and `ConservesAirDuringTransfer`.
- Supporting unit/readout layer: `LengthQuantity`, `VolumeQuantity`, `PressureQuantity`, `AreaQuantity`, `pressureInPascals`, `pressureInPsia`, `lengthInFeet`, `areaInSquareFeet`, `volumeInCubicFeet`, and `temperatureInRankine`.
- Supporting apparatus/figure vocabulary: `GasSpecies`, `Vessel`, `TankBehavior`, `PistonMotionRegime`, `ThermalRegime`, `AirTransferDirection`, `ValveEvent`, `ValvePosition`, `VerticalDirection`, `FigureComponent`, `FigureLabel`, and `HorizontalPlacement`.
- Supporting displayed-choice declarations: `AnswerChoice`, `answerPressureInPsia`, and `recordedAnswerChoice`.
- The blueprint was not edited because the task's write permissions restrict this agent to the assigned Lean file and this report. Review agent: add `\leanok` to the target environment.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `ideal gas equation pressure volume amount temperature` found `IdealGas.ideal_gas_law`, `DimPressure`, and `Temperature`.
- `DimPressure DimArea Dimensionful WithDim` found the four corresponding Physlib declarations.
- `thermodynamic absolute Temperature toReal` and `Temperature.toReal` found `Temperature` and `Temperature.toReal`.
- `amount of substance mole physical dimension` found only generic dimension infrastructure, not a molar-amount physical type.
- `DimLength physical length dimensional quantity` and `DimVolume physical volume dimensional quantity` found `Dimension.L𝓭`, `Dimensionful`, and `WithDim`, but no ready-made `DimLength` or `DimVolume`.
- `pounds per square inch psi pressure unit` found `DimPressure.psi` and `DimArea.squareFoot`.
- `feet foot LengthUnit.feet` and `cubic foot volume unit cubicFoot` found `LengthUnit.feet` and `DimArea.squareFoot`, but no cubic-volume convenience declaration.
- `Rankine temperature unit`, `TemperatureUnit.rankine`, `Temperature.kelvin TemperatureUnit.kelvin`, and `TemperatureUnit.absoluteFahrenheit` established that there is no named Rankine declaration and that `TemperatureUnit.absoluteFahrenheit` is the absolute Fahrenheit scale, defined as `5/9` kelvin.

Source/module data was fetched for the candidates used or evaluated closely: `IdealGas.ideal_gas_law`, `DimPressure`, `DimArea`, `DimPressure.psi`, `DimArea.squareFoot`, `LengthUnit.feet`, `Dimensionful`, `WithDim`, `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and `TemperatureUnit.absoluteFahrenheit`.

## Physlib/Mathlib names grounded

- `DimPressure` and `DimPressure.psi` from `Physlib.Units.WithDim.Pressure`.
- `DimArea` and `DimArea.squareFoot` from `Physlib.Units.WithDim.Area`.
- `LengthUnit.feet`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI` from Physlib's units infrastructure.
- `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic`.
- `TemperatureUnit` and `TemperatureUnit.absoluteFahrenheit` from `Physlib.Thermodynamics.Temperature.TemperatureUnits`.
- `NNReal` and `ℝ` are the Mathlib scalar types underlying the nonnegative physical magnitudes and named scalar readouts.

## Local abstractions introduced

- `LengthQuantity := Dimensionful (WithDim L𝓭 NNReal)` and `VolumeQuantity := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)` retain their physical dimensions while filling gaps where Physlib has no ready-made convenience aliases.
- `RigidTankPistonSetup` keeps the apparatus roles and independent physical unknowns distinct. In particular, it does not collapse pressure, area, length, volume, or temperature to bare reals.
- Molar amounts and the mixed-unit gas constant are explicitly named scalar readouts (`...Moles`, `...PerMoleRankine`) because no compatible amount-of-substance quantity API was found and because the textbook equations are evaluated in one stated mixed-unit system.
- The three law structures preserve piston geometry, ideal-gas inventories, and material conservation as separate physical assumptions rather than hiding the requested answer in a definition.

## Grounding gaps

- `IdealGas.ideal_gas_law` is a near miss: its source is tied to Physlib's statistical-mechanics `IdealGas.pressure`, is unitless, and fixes `R = 1`. It cannot directly express this problem's dimensionful pressures and mixed imperial-unit readouts, so a faithful local inventory-law interface was used.
- No ready-made Physlib `DimLength`, `DimVolume`, cubic-foot volume constant, or dimensionful amount-of-substance/mole type was found.
- Physlib has `TemperatureUnit.absoluteFahrenheit` but no declaration named Rankine; absolute Fahrenheit has the correct zero and degree size for Rankine and is used explicitly.
- The requested `archon dag-query` navigation could not run because `archon` was not on `PATH` in this environment. The chapter contains no dependency labels beyond its single target.
- `.archon/AGENTS.md` and the assigned Lean file were absent at task start. The explicit user role and `.archon/prover-modes/physics-formalize.md` supplied the operative instructions; the assigned file was created.

## Verification

- Lean LSP diagnostics: success, with only the expected theorem `sorry` warning.
- Full check: `lake env lean PhyXMiniProblems/problem_phyx_mini_0448.lean` exited `0`, again with only the expected `sorry` warning.

## Why I stopped

Real progress: one complete physics theorem stub and its supporting dimensionful model were introduced and compile successfully. The autoformalize stage calls for a `by sorry` body rather than a proof.
