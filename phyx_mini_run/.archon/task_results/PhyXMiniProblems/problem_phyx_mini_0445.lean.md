# Autoformalization result: `problem_phyx_mini_0445.lean`

## Assumption/target split

### Governing laws

- `SatisfiesEvaporationAndSteadyFlowLaws.liquidVolumeLossDeterminesEvaporatedMass` states the unit-independent relation `A Δh = ṁ_evap Δt v_liquid`.
- `SatisfiesEvaporationAndSteadyFlowLaws.massConservedThroughValveAndHeater` states that the nitrogen mass-flow rate leaving the heater equals the mass-flow rate evaporated from the container.
- `SatisfiesEvaporationAndSteadyFlowLaws.outletGasVolumeFlowLaw` states `V̇_exit = ṁ_exit v_exit`.
- `SatisfiesNitrogenPropertyModel` relates the independently stored liquid and outlet specific volumes to an external nitrogen property table at the corresponding physical states.
- `lengthInMeters_eq_millimeters_div_thousand` and `timeInMinutes_eq_sixty_mul_hours` are general named-unit conversion lemmas, not problem-specific assumptions.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the Lean theorem assumes no prior subproblem result.

### Figure/data readouts

- `MatchesNitrogenEvaporationScenario` records nitrogen as the substance, liquid in the container, gas at the outlet, evaporation due to heat transfer, constant container cross section, and traversal of the valve and heater.
- `MatchesSuppliedNitrogenHeaterFigure` records the visible liquid-below-vapor regions, container, valve, heater, outlet arrow, the labels `Vapor`, `Liquid N₂`, and `Heater`, and the directed path `container vapor → valve → heater → outlet`.
- `MatchesProblemReadouts` records `100 K`, `0.5 m²`, `30 mm`, `1 h`, `500 kPa`, and `260 K` as calibrated readouts of dimensionful quantities.
- `MatchesReferenceNitrogenPropertyData` records the independent thermodynamic property entries `v_liquid = 0.001452 m³/kg` and `v_exit = 0.1467 m³/kg`.
- `HasPhysicalNitrogenFlowParameters` records positivity of the measured state and flow parameters.

### Current target conclusions

- `outlet_nitrogen_volume_flow_rate` concludes that the exact rate implied by the quoted property precision is `489 / 19360 m³/min = 0.025258264... m³/min`.
- The same theorem concludes that this rounds to displayed choice D, `0.02526 m³/min`, and that D is the unique matching answer at five decimal places.

## Goal-faithfulness audit

`NitrogenEvaporationSetup.outletVolumeFlowRate` is an independent `VolumeFlowRateQuantity`; it is not defined from the answer list, from `489 / 19360`, or from `0.02526`. The scenario, figure, problem-readout, property-model, property-data, and physicality structures contain no requested outlet flow value. The law structure contains only the three general symbolic relations among area, level drop, elapsed time, mass flow, and specific volume.

The values `0.001452 m³/kg` and `0.1467 m³/kg` are state-property readouts at different input states, not an outlet-flow assertion. They become a flow rate only after combination with the independently supplied geometry, elapsed time, and conservation laws. The exact derived value and the rounded choice-D conclusion occur only on the conclusion side of `outlet_nitrogen_volume_flow_rate`.

`displayedOutletFlowInCubicMetersPerMinute` and `recordedDatasetAnswer` preserve answer metadata but are not theorem hypotheses and do not constrain the physical setup. `IsReportedOutletFlowChoice` merely compares an already-derived physical rate to each displayed value at the precision used by the choices.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0445:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0445.outlet_nitrogen_volume_flow_rate`.
- `AreaQuantity`, `LengthQuantity`, `TimeQuantity`, `SpecificVolumeQuantity`, `MassFlowRateQuantity`, and `VolumeFlowRateQuantity` preserve the relevant dimensions and nonnegativity.
- The named-unit readouts preserve square metres, millimetres, hours, kilopascals, kelvins, cubic metres per kilogram, kilograms per unit time, and cubic metres per minute.
- `NitrogenHeaterFigure` plus the figure enums preserve the geometry, labels, and directed connectivity visible in the primary raster.
- `LiquidNitrogenState`, `OutletNitrogenState`, `NitrogenPropertyTable`, and `NitrogenEvaporationSetup` preserve the physical phases, measured states, table interface, container geometry, and independent flow observables.
- The scenario, figure, readout, property-model, reference-data, physicality, and flow-law predicates explicitly separate assumptions from the current conclusion.
- `AnswerChoice`, `displayedOutletFlowInCubicMetersPerMinute`, `recordedDatasetAnswer`, and `IsReportedOutletFlowChoice` represent the multiple-choice layer without using it to determine the physical flow.

The chapter already existed and contains `% archon:physics`. It was not edited to add `\leanok`, because this task's explicit write-permission section forbids editing blueprint chapters; the coordinator should add the marker after accepting the formalization.

## LeanExplore queries and candidates actually used

All searches passed `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical quantity with SI units length area volume time temperature pressure` found `UnitChoices.SI`, `Dimension`, `Dimensionful`, `DimPressure`, and related unit infrastructure.
- `PhysLean Dimensionful SI units` confirmed `Dimensionful` (id 394284) and `UnitChoices.SI` (id 394270). Their source and modules were fetched before use.
- `thermodynamics specific volume density mass flow rate volumetric flow rate` returned `FluidDynamics.MassDensity`, `FluidDynamics.FluidState`, `IdealGas.ideal_gas_law`, and the Navier--Stokes continuity equation, but no lumped dimensionful specific-volume, mass-flow, or volume-flow alias suitable for this control-volume problem.
- `Temperature absolute thermodynamic temperature kelvin TemperatureUnit` found `Temperature` (id 394201), `TemperatureUnit` (id 394233), and `TemperatureUnit.kelvin` (id 394250). Source and module information were fetched for all three.
- `LengthUnit TimeUnit MassUnit meters minutes kilograms` and `TimeUnit.hours LengthUnit.millimeters LengthUnit.meters MassUnit.kilograms` grounded the named-unit types and constants. Source/module information was fetched for `LengthUnit`, `MassUnit`, and `TimeUnit.minutes`; local source inspection and an LSP snippet verified `TimeUnit.hours`, `TimeUnit.minutes`, `LengthUnit.millimeters`, and `MassUnit.kilograms` with their exact types.
- `nonnegative real numbers NNReal` found `NNReal` (id 211536); its source and module were fetched before using it as the magnitude type inside `WithDim`.
- `DimPressure` (id 394474) was source-checked and confirmed as Physlib's dimensionful `M L⁻¹ T⁻²` pressure type.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Physlib: `DimPressure`.
- Physlib: `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- Physlib: `LengthUnit`, `LengthUnit.meters`, `LengthUnit.millimeters`, `TimeUnit`, `TimeUnit.hours`, `TimeUnit.minutes`, `MassUnit`, and `MassUnit.kilograms`.
- Mathlib: `NNReal`, `ℝ`, `round`, rational numerals, and finite/decidable derivations.

## Local abstractions introduced

- Physlib `Dimensionful (WithDim ... NNReal)` aliases were introduced for the nonnegative quantities for which no suitable native alias was found: area, length, time, specific volume, mass flow, and volume flow. These retain their full physical dimensions rather than collapsing them to scalar aliases or one-field wrappers.
- `NitrogenPropertyTable` is the smallest state-property interface needed for the two lookup roles absent from the searched API. It maps physical temperature, pressure, and temperature inputs to a dimensionful specific volume.
- `NitrogenHeaterFigure` is a qualitative figure interface that preserves phase placement, object labels, and flow-path topology without inserting any numeric result.
- `SatisfiesEvaporationAndSteadyFlowLaws` is a local governing-law interface because the search results concerned continuum field equations or ideal gases rather than this lumped evaporation/heater balance. Its fields are quantified over compatible units and contain no answer-specific constants.

## Grounding gaps and redraft requests

- The source extraction dropped the unit after every answer choice. `m³/min` is inferred because the stated data and the reference nitrogen specific volumes give `0.025258... m³/min`, which rounds to recorded choice D. A source redraft should restore the printed answer unit explicitly.
- The blueprint/source report does not cite the nitrogen property table or print the two specific-volume entries needed to make the calculation determinate. The formalization exposes them as independent reference-data assumptions rather than hiding them in a definition. A redraft should cite the intended table and confirm `0.001452 m³/kg` at `100 K` and `0.1467 m³/kg` at `500 kPa`, `260 K`.
- LeanExplore found no suitable native lumped `SpecificVolumeQuantity`, `MassFlowRateQuantity`, or `VolumeFlowRateQuantity`, and no directly applicable finite-control-volume evaporation/heater theorem. The local dimensionful aliases and explicit governing-law predicate cover these gaps.
- `FluidDynamics.NavierStokes.ClassicalContinuityEquation` is a continuum PDE over fields and is not a faithful drop-in replacement for the steady lumped mass balance used here. `IdealGas.ideal_gas_law` also does not supply the reference-property lookup used by the recorded answer.
- The requested `.archon/AGENTS.md` file is absent. The injected role instructions and `.archon/prover-modes/physics-formalize.md` were followed instead.
- The `archon` executable was not available on `PATH`, so the optional read-only blueprint dependency-graph query could not be run.

## Verification

- `archon-lean-lsp` diagnostics reported only three expected `declaration uses sorry` warnings: the two general unit-conversion lemmas and the target theorem; there were no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0445.lean` exited successfully with the same three expected warnings.
