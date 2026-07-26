# Autoformalization result: `problem_phyx_mini_0354.lean`

## Assumption/target split

### Governing laws

- Every labelled state obeys the SI-readout ideal-gas equation
  `p V = n R T`.
- Monatomic argon obeys `U = (3/2) n R T`.
- Quasistatic boundary work on a straight directed leg is the source pressure
  times the volume change. This gives zero work on the vertical isochoric legs
  and the usual `p ΔV` work on each horizontal isobaric leg once combined with
  the figure relations.
- With heat positive into the gas and work positive out of the gas, the first
  law on each leg is `Q = ΔU + W`.
- The mole amount, gas constant, pressure, volume, and absolute temperature
  readouts are positive.

These assumptions are represented by `SatisfiesMonatomicIdealGasCycleLaws`
and `HasPhysicalCycleParameters`. Neither predicate mentions an efficiency
value or an answer choice.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- The sample is `4.00 mol` of low-pressure ideal monatomic argon.
- The measured temperatures at `a`, `b`, `c`, and `d` are respectively
  `250.0 K`, `300.0 K`, `380.0 K`, and `316.7 K`. They are modeled as
  one-decimal readouts with half-unit-in-the-last-place tolerance `0.05 K`,
  avoiding an inconsistent exact identification of the rounded `316.7 K`.
- The primary image contains vertices `a,b,c,d`, axes `p,V`, origin `O`, and
  directed legs `a -> b -> c -> d -> a`.
- Its left and right legs are vertical/isochoric, its top and bottom legs are
  horizontal/isobaric, the right volume exceeds the left volume, and the upper
  pressure exceeds the lower pressure.

These are represented by `MatchesArgonSampleAndTemperatureReadouts` and
`MatchesSuppliedRectangularCycle`.

### Current target conclusions

- Dimensionless efficiency `thermalEfficiency setup = 1 / 16`.
- Percentage efficiency `thermalEfficiencyPercent setup = 25 / 4`, i.e.
  `6.25%`.
- Agreement with displayed answer choice B.

All three conclusions occur only in `problem_phyx_mini_0354`.

## Goal-faithfulness audit

- `ArgonHeatEngineSetup` stores physical states, temperatures, internal
  energies, signed leg heats, and signed leg works, but has no efficiency or
  selected-answer field.
- `thermalEfficiency` is independently defined by the standard physical ratio
  `W_net / Q_in`; it is not defined as `1/16`.
- `totalHeatInputInJoules` sums the positive parts of all signed leg heats, so
  the formalization does not assume in advance which legs absorb heat.
- Neither premise structure contains `1/16`, `25/4`, choice B, or the target
  equality.
- `displayedEfficiencyPercent` merely transcribes the four printed choices.
  Unfolding the table does not establish that the independently computed
  efficiency equals choice B.
- The figure equalities and general thermodynamic laws require the future
  prover to derive the net work, identify the positive heat-transfer legs, and
  evaluate the ratio. No local definition makes the target true by unfolding.

## Declarations created and blueprint mapping

- Physical quantities/readouts: `VolumeQuantity`, `volumeInCubicMeters`,
  `pressureInPascals`, `energyInJoules`, and `temperatureInKelvin`.
- Figure vocabulary: `CycleState`, `CycleLeg`, `LegConstraint`,
  `DiagramLabel`, `legSource`, `legTarget`, `displayedLegConstraint`,
  `PressureVolumeCycleFigure`, and `MatchesSuppliedRectangularCycle`.
- Experiment data: `GasSpecies`, `GasModel`, `ArgonHeatEngineSetup`, the named
  scalar readout functions, `MatchesTemperatureReadout`,
  `MatchesArgonSampleAndTemperatureReadouts`, and
  `HasPhysicalCycleParameters`.
- Governing-law interface: `SatisfiesMonatomicIdealGasCycleLaws`.
- Efficiency/answers: `netCycleWorkInJoules`, `totalHeatInputInJoules`,
  `thermalEfficiency`, `thermalEfficiencyPercent`, `AnswerChoice`,
  `displayedEfficiencyPercent`, and `IsDisplayedEfficiencyAnswer`.
- Blueprint label `thm:physics:phyx_mini_0354:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0354.problem_phyx_mini_0354`.

The blueprint chapter was not edited because the task's final explicit write
permissions forbid blueprint edits. The coordinator/review step should add or
synchronize `\leanok` after accepting the declaration.

## LeanExplore queries/candidates actually used

All searches passed `packages: ["Mathlib", "Physlib"]`.

- `ideal gas law pressure volume amount temperature thermodynamics` found
  `IdealGas.ideal_gas_law`, `Temperature.toReal`, and `DimPressure`.
- `thermodynamic heat engine cycle efficiency net work heat input` and
  `molar heat capacity monatomic ideal gas constant volume constant pressure`
  found statistical-mechanics heat/internal-energy declarations but no
  suitable finite-cycle heat-engine or efficiency interface.
- `Temperature Pressure Volume Energy SI units` found `UnitChoices.SI`,
  `UnitChoices.SI_temperature`, `Temperature.toReal`, and `DimPressure`.
- Likely-name queries `TemperatureUnit.kelvin`, `DimEnergy`, and
  `Dimensionful WithDim physical quantity dimensions` confirmed the unit and
  dimensional-quantity APIs used in the file.
- `Finite sum over an enum Fintype` confirmed `Finset.sum` for the cycle-leg
  sums.

Source and module data were fetched for the candidates assessed for direct
use: `IdealGas.ideal_gas_law`, `Temperature.toReal`, `DimPressure`,
`UnitChoices.SI`, `UnitChoices.SI_temperature`, `TemperatureUnit.kelvin`,
`DimEnergy`, `Dimensionful`, and `Finset.sum`.

## Physlib/Mathlib names grounded

- Physlib: `Temperature`, `Temperature.toReal`, `TemperatureUnit`,
  `TemperatureUnit.kelvin`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `DimPressure`, `DimEnergy`, `UnitChoices`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, real absolute value, `max`, `Fintype`, and finite sum
  notation backed by `Finset.sum`.
- `IdealGas.ideal_gas_law` was inspected but not used: its source explicitly
  uses a unitless statistical-mechanics model with `R = 1`, whereas this
  problem requires dimensionful pressure/volume and SI mole/kelvin readouts.

## Local abstractions introduced

- `VolumeQuantity` is the minimal Physlib dimensional object
  `Dimensionful (WithDim L^3 NNReal)`, not a transparent scalar alias.
- The amount of substance remains an abstract type with an explicit mole
  readout, so the physical sample is not collapsed to a bare real.
- `PressureVolumeCycleFigure` and the label/leg enums retain the image's
  geometry and directed process order without encoding any target answer.
- `SatisfiesMonatomicIdealGasCycleLaws` is an SI-readout adapter for the
  governing thermodynamic laws absent from the available compatible Physlib
  API. It states general laws rather than the requested efficiency formula.
- `MatchesTemperatureReadout` preserves the experimental role of the stated
  one-decimal temperatures and the rounding of `316.7 K`.

## Grounding gaps and redraft requests

- No compatible Physlib API was found for a dimensionful finite heat-engine
  cycle, quasistatic `p dV` work, first-law leg bookkeeping, total heat input,
  or thermal efficiency. These are represented by the smallest local setup and
  law interfaces needed by the source.
- The recorded answer appears inconsistent with the standard monatomic
  ideal-gas model. Temperatures `250`, `300`, `380`, and `950/3` K satisfy the
  rectangular ideal-gas constraint and all four stated one-decimal readouts.
  They give heat input `275 nR`, net work `(40/3) nR`, and therefore efficiency
  `8/165 ≈ 4.85%`, not `1/16 = 6.25%`. Thus the by-sorry target is faithfully
  recorded but is not expected to be provable from the non-smuggled physical
  assumptions. The plan/review agent should verify the dataset answer or
  redraft the target/model before the proof stage.
- The requested `.archon/AGENTS.md` does not exist in this checkout. The
  available `.archon/prover-modes/physics-formalize.md` and the injected role
  instructions were read and followed.
- The `archon` executable was not available on `PATH`, so the optional DAG
  queries could not run. The chapter declares no dependency labels beyond its
  own target.
- The assigned Lean file did not exist initially, so there were no
  file-specific `/- USER: ... -/` comments to apply.

## Verification

- `archon-lean-lsp` reports no errors and exactly one expected
  `declaration uses sorry` warning at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0354.lean` exits
  successfully with the same warning.
