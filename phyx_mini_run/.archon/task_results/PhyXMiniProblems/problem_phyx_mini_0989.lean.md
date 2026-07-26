# Autoformalization result: `problem_phyx_mini_0989.lean`

Archon iteration 003 performed a fresh post-formalization audit of the
dimensionful series-RL model. The exact gate reason is evidence-only: the
reviewer had not accepted a genuine post-formalization task result. The source,
primary raster, blueprint, Lean declarations, library grounding, and compiler
diagnostics were therefore checked again in this iteration. No semantic defect
or declaration redraft was found, so the assigned Lean file was preserved.

## Assumption/target split

### Governing laws

- An ideal infinite-input-resistance voltmeter draws no current.
- The named long-time current and external-resistor voltage are limits of the
  corresponding transient observables.
- The external resistor obeys Ohm's law during the transient and at long times.
- The steady series loop obeys Kirchhoff's voltage law with battery internal
  resistance, external resistance, and solenoid winding resistance.
- The series-RL time constant obeys `tau = L / R_total`.
- The resistor voltage follows the standard rising exponential with its
  long-time voltage as asymptote.
- The long-time magnetic energy obeys the general law `U = (1/2) L I^2`.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- Written apparatus/data: a `50 ohm` external resistor, a `25 V` battery with
  negligible internal resistance, `v_R(0+) = 0 V`, and long-time
  `v_R = 25 V`.
- Written roles/topology: battery, switch, external resistor, solenoid, and
  ideal voltmeter in one series loop, with the voltmeter across the external
  resistor.
- Direct iteration-003 inspection of `phyx_data/test_image/989.png`: horizontal
  `t (ms)` axis over `0..15`, vertical `v_R (V)` axis over `0..25`, grid
  spacings `2.5 ms` and `5 V`, and thirteen black samples at integer times
  `2..14 ms` forming an increasing, concave-down trace.
- Figure-analysis readouts: a `25 V` asymptote and an `8 ms` fitted time
  constant. In particular, the sample near `8 ms` is about `16 V`, consistent
  with `25 * (1 - exp (-8/8))`. These readouts calibrate independent voltage
  and time-constant fields; they do not state an inductance or energy.

### Current target conclusions

- `energyInJoules setup.longTimeStoredMagneticEnergy = 1 / 20`, namely
  `0.050 J`.
- Answer choice B is the unique exact match among the four displayed energies.

## Goal-faithfulness audit

The requested energy is the independent `DimEnergy` field
`SeriesSolenoidCircuit.longTimeStoredMagneticEnergy`. No hypothesis assigns it
`1 / 20`, and no setup field or local definition constructs it from the answer
table or `recordedDatasetAnswer`. The only premise involving its value is the
generic constitutive law `U = (1/2) L I^2` in
`SatisfiesIdealSeriesRLaws.longTimeMagneticEnergyLaw`.

The inductance and winding resistance are also independent dimensionful fields.
Neither `MatchesStatedMeasurements` nor `MatchesSuppliedVoltageTimeGraph`
assumes `L = 0.4 H`, winding resistance `= 0 ohm`, or the target energy. A later
proof must instead derive `I_infinity = 0.5 A` from the long-time resistor
readout and Ohm's law, infer zero winding resistance from Kirchhoff balance,
convert `8 ms` to `0.008 s`, derive `L = 0.4 H` from the time-constant law, and
only then compute `U = 0.050 J`.

`displayedEnergyInJoules` merely transcribes all four source choices.
`recordedDatasetAnswer := .B` is metadata and is not used by a premise, law, or
the target definition. Thus neither the numerical energy equality nor the
unique-choice conclusion is smuggled into the assumptions or made true by
unfolding a local definition.

## Source/law/answer audit

- **Source facts:** apparatus roles, the `50 ohm` and `25 V` labels, endpoint
  voltages, graph axes, black samples, and the fitted `8 ms` time constant occur
  only in the scenario/data/graph predicates.
- **Physical laws:** ideal-voltmeter behavior, limit relations, Ohm's law,
  Kirchhoff balance, `tau = L / R_total`, the rising exponential, and
  `U = (1/2) L I^2` are generic fields of `SatisfiesIdealSeriesRLaws` and do not
  contain the requested numerical answer.
- **Recorded answer:** choice B is retained only as unused dataset metadata.
  The theorem conclusion independently states both the energy and uniqueness.

## Declarations and blueprint labels

All declarations are in namespace
`PhyXMiniProblems.ProblemPhyXMini0989`. The blueprint now has an explicit
environment for every public declaration.

### Main target

- `problem_phyx_mini_0989` ->
  `thm:physics:phyx_mini_0989:target`.

### Dimension and readout layer

The label prefix below is
`def:physics:phyx-mini-0989:phyxminiproblems-problemphyxmini0989-`.

- `electricCurrentDimension` -> `electriccurrentdimension`.
- `electricPotentialDimension` -> `electricpotentialdimension`.
- `electricalResistanceDimension` -> `electricalresistancedimension`.
- `electricalInductanceDimension` -> `electricalinductancedimension`.
- `TimeQuantity` -> `timequantity`.
- `VoltageQuantity` -> `voltagequantity`.
- `ResistanceQuantity` -> `resistancequantity`.
- `InductanceQuantity` -> `inductancequantity`.
- `ElectricCurrentQuantity` -> `electriccurrentquantity`.
- `nonnegativeReadout` -> `nonnegativereadout`.
- `timeReadout` -> `timereadout`.
- `timeInSeconds` -> `timeinseconds`.
- `timeInMilliseconds` -> `timeinmilliseconds`.
- `voltageInVolts` -> `voltageinvolts`.
- `resistanceInOhms` -> `resistanceinohms`.
- `inductanceInHenries` -> `inductanceinhenries`.
- `currentInAmperes` -> `currentinamperes`.
- `energyInJoules` -> `energyinjoules`.

### Apparatus, graph, setup, and premises

These use the same definition-label prefix.

- `CircuitComponent` -> `circuitcomponent`.
- `ComponentModel` -> `componentmodel`.
- `CircuitTopology` -> `circuittopology`.
- `VoltmeterConnection` -> `voltmeterconnection`.
- `SwitchState` -> `switchstate`.
- `GraphAxisLabel` -> `graphaxislabel`.
- `DataMarker` -> `datamarker`.
- `TraceShape` -> `traceshape`.
- `ResistorVoltageTimeGraph` -> `resistorvoltagetimegraph`.
- `SeriesSolenoidCircuit` -> `seriessolenoidcircuit`.
- `MatchesWrittenScenario` -> `matcheswrittenscenario`.
- `MatchesStatedMeasurements` -> `matchesstatedmeasurements`.
- `MatchesSuppliedVoltageTimeGraph` -> `matchessuppliedvoltagetimegraph`.
- `HasPhysicalSeriesRLParameters` -> `hasphysicalseriesrlparameters`.
- `SatisfiesIdealSeriesRLaws` -> `satisfiesidealseriesrlaws`.

### Later-proof milestones

The label prefix below is
`lem:physics:phyx-mini-0989:phyxminiproblems-problemphyxmini0989-`.

- `timeInMilliseconds_eq_thousand_mul_timeInSeconds` ->
  `timeinmilliseconds-eq-thousand-mul-timeinseconds`.
- `longTimeSeriesCurrent_eq_halfAmpere` ->
  `longtimeseriescurrent-eq-halfampere`.
- `solenoidWindingResistance_eq_zeroOhms` ->
  `solenoidwindingresistance-eq-zeroohms`.
- `solenoidInductance_eq_twoFifthsHenry` ->
  `solenoidinductance-eq-twofifthshenry`.

### Multiple-choice layer

These use the definition-label prefix above.

- `AnswerChoice` -> `answerchoice`.
- `displayedEnergyInJoules` -> `displayedenergyinjoules`.
- `recordedDatasetAnswer` -> `recordeddatasetanswer`.
- `MatchesLongTimeStoredEnergy` -> `matcheslongtimestoredenergy`.
- `IsUniqueMatchingAnswer` -> `isuniquematchinganswer`.

Every listed environment is ready for the deterministic blueprint-marker sync.
The blueprint itself was not edited because prover write permissions explicitly
restrict this lane to the assigned Lean file and task-result report.

## LeanExplore queries/candidates actually used

Every iteration-003 search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `series RL circuit resistor voltage exponential transient and energy stored in an inductor`:
  used `Real.exp` (id `128207`) for the transient and `DimEnergy`
  (id `394468`) for the energy observable; no circuit-law declaration was
  returned.
- Likely-name query `Dimensionful WithDim physical quantity SI units`: used
  `Dimensionful` (id `394284`), `UnitChoices.SI` (id `394270`), and
  `Dimension` (id `394292`).
- Likely-name query `WithDim`: used `WithDim` (id `394425`).
- Natural-language/likely-name query `Dimension.Cd electric charge dimension`
  (with the Unicode declaration name in the actual call): used
  `Dimension.Cd`/`Dimension.C𝓭` (id `394337`).
- Likely-name query `TimeUnit milliseconds seconds conversion`: used
  `TimeUnit.milliseconds` (id `393635`) and `TimeUnit.seconds` (id `393630`).
- Likely-name query `DimEnergy joule energy readout`: used `DimEnergy`
  (id `394468`); `DimEnergy.joule` (id `394469`) was considered, while the file
  retains its direct coherent-SI projection.
- Likely-name query
  `DimVoltage DimResistance DimInductance DimCurrent DimTime`: returned the
  foundational `Dimension`, `DimEnergy`, `WithDim`, and `Dimension.T𝓭`, but no
  ready-made voltage, resistance, inductance, current, or time magnitude aliases.
- Natural-language query
  `Ohm's law Kirchhoff voltage law series RL time constant`: returned unrelated
  algebraic and field-theory declarations, confirming that a local lumped-circuit
  law interface is still required.

Source, module, and docstring were fetched in this iteration only for candidates
actually retained by the model: `Dimension`, `Dimension.C𝓭`, `Dimensionful`,
`WithDim`, `UnitChoices.SI`, `DimEnergy`, `TimeUnit.seconds`,
`TimeUnit.milliseconds`, and `Real.exp`.

## Physlib/Mathlib names grounded

- Physlib `Physlib.Units.Dimension`: `Dimension` and `Dimension.C𝓭`.
- Physlib `Physlib.Units.Basic`: `Dimensionful` and `UnitChoices.SI`.
- Physlib `Physlib.Units.WithDim.Basic`: `WithDim`.
- Physlib `Physlib.Units.WithDim.Energy`: `DimEnergy`.
- Physlib `Physlib.SpaceAndTime.Time.TimeUnit`: `TimeUnit.seconds` and
  `TimeUnit.milliseconds`.
- Mathlib `Mathlib.Analysis.Complex.Exponential`: `Real.exp`.
- The compiled file also uses the standard Mathlib names `NNReal`,
  `Filter.Tendsto`, `Filter.atTop`, and `Topology.nhds`.

## Local abstractions introduced

- Electrical dimensions are composed from Physlib base dimensions: current is
  `C T^-1`, voltage is energy per charge, resistance is voltage per current,
  and inductance is resistance times time. This preserves dimensions rather
  than collapsing the physical magnitudes to transparent real aliases.
- Voltage, resistance, inductance, time, and current use
  `Dimensionful (WithDim ... NNReal)`; energy uses Physlib's `DimEnergy`.
  Real values appear only through explicitly named coherent-unit readouts,
  graph metadata, function arguments measured in seconds, and answer labels.
- Circuit components/models, topology, switch state, meter placement, graph
  vocabulary, and `SeriesSolenoidCircuit` are local because no suitable Physlib
  lumped-circuit object was found. They preserve the apparatus roles and keep
  the physical observables independent.
- `MatchesWrittenScenario`, `MatchesStatedMeasurements`,
  `MatchesSuppliedVoltageTimeGraph`, `HasPhysicalSeriesRLParameters`, and
  `SatisfiesIdealSeriesRLaws` deliberately separate qualitative setup, source
  data, raster-derived fit data, passivity, and governing laws.

## Grounding gaps and redraft requests

- No ready-made Physlib declaration was found for voltage/resistance/current/
  inductance magnitude types, ohm or henry readouts, a series-RL circuit,
  Ohm's law, Kirchhoff's voltage law, the RL time-constant law, or inductor
  magnetic energy. The local dimensional quantities and law predicate are the
  smallest faithful interface found for this source.
- The requested `.archon/AGENTS.md` is absent in this checkout. The local
  `.archon/prover-modes/physics-formalize.md` and the injected prover-role
  instructions agree on the applicable workflow and write restrictions.
- The advertised `archon` DAG executable is not on `PATH`. The blueprint's
  explicit `uses` graph was inspected directly, so this did not block the
  standalone formalization audit.
- No redraft is requested. The review reason concerns missing evidence only,
  and the iteration-003 source/law/answer audit found no goal-smuggling or
  physics-model defect.

## Verification

- Iteration-003 Lean LSP diagnostics succeeded with exactly five expected
  `declaration uses sorry` warnings, for the four later-proof lemmas and the
  main target theorem, and no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0989.lean` exited `0` in
  iteration 003 with exactly the same five warnings and no errors.
