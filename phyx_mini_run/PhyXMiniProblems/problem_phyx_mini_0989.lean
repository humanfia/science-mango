import Mathlib
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0989

open Dimension Filter Topology

/-!
# Energy stored by the solenoid in a switched series RL circuit

A solenoid with unknown winding resistance and inductance is connected in
series with a `50.0 Ω` resistor, an ideal `25.0 V` battery, and a switch.  An
ideal voltmeter records the external-resistor voltage after the switch closes.
The primary graph `989.png` contains thirteen black samples from `2 ms` through
`14 ms`; a standard rising-exponential fit has an `8 ms` time constant and a
`25 V` asymptote.  The stated endpoint measurements are `v_R(0⁺) = 0 V` and
`v_R(∞) = 25 V`.

Voltage, resistance, inductance, time, current, and energy retain their physical
dimensions below.  Real numbers occur only at explicit unit-readout boundaries,
in graph metadata, and in answer-choice labels.  In particular, the long-time
stored energy is an independent observable constrained by the magnetic-energy
law; it is not defined from the recorded answer.

Assumption/target split:

* governing laws: ideal voltmeter behavior, long-time limits, Ohm's law,
  steady-state Kirchhoff balance, the series-RL time constant, the rising
  exponential transient, and `U = (1/2) L I²`;
* previous-part results: none;
* figure/data readouts: the axis labels and scales, thirteen black samples,
  `25 V` fitted asymptote, `8 ms` fitted time constant, and the numerical data
  stated in the prose;
* current target: the independent long-time energy is `0.050 J`, uniquely
  matching displayed answer choice B.
-/

/-! ## Physical dimensions, quantities, and unit readouts -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has dimension potential difference per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Electrical inductance has dimension resistance times time. -/
def electricalInductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent voltage magnitude. -/
abbrev VoltageQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- A nonnegative current magnitude in the orientation of the series loop. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Read a nonnegative dimensionful quantity in the selected coherent units. -/
def nonnegativeReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read an elapsed time in the selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  nonnegativeReadout {UnitChoices.SI with time := unit} time

/-- Read an elapsed time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Read an elapsed time in milliseconds. -/
def timeInMilliseconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.milliseconds time

/-- Read a voltage magnitude in volts. -/
def voltageInVolts (voltage : VoltageQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI voltage

/-- Read a resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI resistance

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI inductance

/-- Read a current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI current

/-- Read Physlib's dimensionful energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Circuit roles and primary-graph vocabulary -/

/-- Components named in the written series-circuit setup. -/
inductive CircuitComponent where
  | battery
  | switch
  | externalResistor
  | solenoid
  | voltmeter
  deriving DecidableEq, Fintype, Repr

/-- Lumped models assigned to the named circuit components. -/
inductive ComponentModel where
  | idealVoltageSourceWithNegligibleInternalResistance
  | idealSwitch
  | idealOhmicResistor
  | solenoidWithWindingResistanceAndInductance
  | idealInfiniteInputResistanceVoltmeter
  | other
  deriving DecidableEq, Repr

/-- Connectivity distinguished by this problem. -/
inductive CircuitTopology where
  | batterySwitchResistorSolenoidInOneSeriesLoop
  | other
  deriving DecidableEq, Repr

/-- The only meter connection used in the scenario. -/
inductive VoltmeterConnection where
  | acrossExternalResistor
  | other
  deriving DecidableEq, Repr

/-- Ideal switch state as a function of time. -/
inductive SwitchState where
  | openCircuit
  | closedCircuit
  deriving DecidableEq, Repr

/-- Axis meanings printed on the primary graph. -/
inductive GraphAxisLabel where
  | elapsedTimeMilliseconds
  | resistorVoltageVolts
  deriving DecidableEq, Repr

/-- Marker style used for every measured point in `989.png`. -/
inductive DataMarker where
  | blackDot
  | other
  deriving DecidableEq, Repr

/-- Qualitative shape of the measured transient. -/
inductive TraceShape where
  | increasingConcaveDownTowardAsymptote
  | other
  deriving DecidableEq, Repr

/-!
Literal graph metadata and calibrated sample readouts.  The fitted asymptote
and time constant are data-analysis readouts of the black-dot trace, not the
requested energy or an encoded inductance.
-/
structure ResistorVoltageTimeGraph where
  horizontalAxisLabel : GraphAxisLabel
  verticalAxisLabel : GraphAxisLabel
  horizontalMinimumMilliseconds : ℝ
  horizontalMaximumMilliseconds : ℝ
  horizontalGridSpacingMilliseconds : ℝ
  verticalMinimumVolts : ℝ
  verticalMaximumVolts : ℝ
  verticalGridSpacingVolts : ℝ
  sampleMarker : Fin 13 → DataMarker
  sampleTimeMilliseconds : Fin 13 → ℝ
  sampleVoltageVolts : Fin 13 → ℝ
  fittedAsymptoteVolts : ℝ
  fittedTimeConstantMilliseconds : ℝ
  traceShape : TraceShape

/-!
The physical circuit and its independent observables.  The real argument of
the transient functions is elapsed time in seconds.  Long-time current,
resistor voltage, and stored energy are fields rather than definitions made
from the expected answer.
-/
structure SeriesSolenoidCircuit where
  componentModel : CircuitComponent → ComponentModel
  topology : CircuitTopology
  voltmeterConnection : VoltmeterConnection
  batteryVoltage : VoltageQuantity
  batteryInternalResistance : ResistanceQuantity
  externalResistorResistance : ResistanceQuantity
  solenoidWindingResistance : ResistanceQuantity
  solenoidInductance : InductanceQuantity
  transientTimeConstant : TimeQuantity
  switchStateAtSeconds : ℝ → SwitchState
  seriesCurrentAtSeconds : ℝ → ElectricCurrentQuantity
  externalResistorVoltageAtSeconds : ℝ → VoltageQuantity
  voltmeterCurrentAtSeconds : ℝ → ElectricCurrentQuantity
  longTimeSeriesCurrent : ElectricCurrentQuantity
  longTimeExternalResistorVoltage : VoltageQuantity
  longTimeStoredMagneticEnergy : DimEnergy
  figure : ResistorVoltageTimeGraph

/-! ## Apparatus assumptions and measured data -/

/-- Qualitative component roles, series topology, and switching protocol. -/
structure MatchesWrittenScenario (setup : SeriesSolenoidCircuit) : Prop where
  batteryModel :
    setup.componentModel .battery =
      .idealVoltageSourceWithNegligibleInternalResistance
  switchModel : setup.componentModel .switch = .idealSwitch
  resistorModel :
    setup.componentModel .externalResistor = .idealOhmicResistor
  solenoidModel :
    setup.componentModel .solenoid =
      .solenoidWithWindingResistanceAndInductance
  voltmeterModel :
    setup.componentModel .voltmeter =
      .idealInfiniteInputResistanceVoltmeter
  seriesTopology :
    setup.topology = .batterySwitchResistorSolenoidInOneSeriesLoop
  meterAcrossResistor :
    setup.voltmeterConnection = .acrossExternalResistor
  switchOpenBeforeClosing : ∀ t : ℝ, t < 0 →
    setup.switchStateAtSeconds t = .openCircuit
  switchClosedFromZero : ∀ t : ℝ, 0 ≤ t →
    setup.switchStateAtSeconds t = .closedCircuit

/-!
Numerical data stated in the prose.  The solenoid's winding resistance and
inductance are deliberately absent: they are unknown parameters inferred from
the steady and transient measurements.
-/
structure MatchesStatedMeasurements (setup : SeriesSolenoidCircuit) : Prop where
  externalResistanceOhms :
    resistanceInOhms setup.externalResistorResistance = 50
  batteryVoltageVolts : voltageInVolts setup.batteryVoltage = 25
  negligibleBatteryInternalResistance :
    resistanceInOhms setup.batteryInternalResistance = 0
  justAfterClosingResistorVoltage :
    voltageInVolts (setup.externalResistorVoltageAtSeconds 0) = 0
  longTimeResistorVoltage :
    voltageInVolts setup.longTimeExternalResistorVoltage = 25

/-!
Primary-raster evidence from `989.png`, including the plotted axes, thirteen
black samples at integer millisecond times `2,...,14`, their calibration to
the physical voltage trace, and the `8 ms` time constant obtained by fitting
the standard rising exponential with a `25 V` asymptote.
-/
structure MatchesSuppliedVoltageTimeGraph
    (setup : SeriesSolenoidCircuit) : Prop where
  horizontalLabel :
    setup.figure.horizontalAxisLabel = .elapsedTimeMilliseconds
  verticalLabel :
    setup.figure.verticalAxisLabel = .resistorVoltageVolts
  horizontalRange :
    setup.figure.horizontalMinimumMilliseconds = 0 ∧
      setup.figure.horizontalMaximumMilliseconds = 15
  horizontalGridSpacing :
    setup.figure.horizontalGridSpacingMilliseconds = 5 / 2
  verticalRange :
    setup.figure.verticalMinimumVolts = 0 ∧
      setup.figure.verticalMaximumVolts = 25
  verticalGridSpacing : setup.figure.verticalGridSpacingVolts = 5
  blackDotSamples : ∀ i, setup.figure.sampleMarker i = .blackDot
  integerMillisecondSampleTimes : ∀ i,
    setup.figure.sampleTimeMilliseconds i = (i.1 : ℝ) + 2
  samplesCalibratePhysicalTrace : ∀ i,
    setup.figure.sampleVoltageVolts i =
      voltageInVolts
        (setup.externalResistorVoltageAtSeconds
          (setup.figure.sampleTimeMilliseconds i / 1000))
  risingExponentialShape :
    setup.figure.traceShape = .increasingConcaveDownTowardAsymptote
  fittedAsymptote : setup.figure.fittedAsymptoteVolts = 25
  fittedTimeConstant : setup.figure.fittedTimeConstantMilliseconds = 8
  fittedTimeConstantCalibratesPhysicalTime :
    timeInMilliseconds setup.transientTimeConstant =
      setup.figure.fittedTimeConstantMilliseconds

/-- Sign and nondegeneracy conditions for the passive physical parameters. -/
structure HasPhysicalSeriesRLParameters
    (setup : SeriesSolenoidCircuit) : Prop where
  sourcePositive : 0 < voltageInVolts setup.batteryVoltage
  externalResistancePositive :
    0 < resistanceInOhms setup.externalResistorResistance
  batteryInternalResistanceNonnegative :
    0 ≤ resistanceInOhms setup.batteryInternalResistance
  windingResistanceNonnegative :
    0 ≤ resistanceInOhms setup.solenoidWindingResistance
  inductancePositive : 0 < inductanceInHenries setup.solenoidInductance
  timeConstantPositive : 0 < timeInSeconds setup.transientTimeConstant
  storedEnergyNonnegative :
    0 ≤ energyInJoules setup.longTimeStoredMagneticEnergy

/-! ## Governing ideal series-RL laws -/

/-!
The uniform lumped-circuit laws used in the solution.  No field gives a
numerical value for the inductance or stored energy.
-/
structure SatisfiesIdealSeriesRLaws
    (setup : SeriesSolenoidCircuit) : Prop where
  idealVoltmeterDrawsNoCurrent : ∀ t : ℝ,
    currentInAmperes (setup.voltmeterCurrentAtSeconds t) = 0
  currentConvergesToLongTimeValue :
    Tendsto
      (fun t : ℝ => currentInAmperes (setup.seriesCurrentAtSeconds t))
      atTop
      (nhds (currentInAmperes setup.longTimeSeriesCurrent))
  resistorVoltageConvergesToLongTimeValue :
    Tendsto
      (fun t : ℝ =>
        voltageInVolts (setup.externalResistorVoltageAtSeconds t))
      atTop
      (nhds (voltageInVolts setup.longTimeExternalResistorVoltage))
  externalResistorOhmsLaw : ∀ t : ℝ, 0 ≤ t →
    voltageInVolts (setup.externalResistorVoltageAtSeconds t) =
      currentInAmperes (setup.seriesCurrentAtSeconds t) *
        resistanceInOhms setup.externalResistorResistance
  longTimeExternalResistorOhmsLaw :
    voltageInVolts setup.longTimeExternalResistorVoltage =
      currentInAmperes setup.longTimeSeriesCurrent *
        resistanceInOhms setup.externalResistorResistance
  longTimeKirchhoffVoltageLaw :
    voltageInVolts setup.batteryVoltage =
      currentInAmperes setup.longTimeSeriesCurrent *
        (resistanceInOhms setup.batteryInternalResistance +
          resistanceInOhms setup.externalResistorResistance +
          resistanceInOhms setup.solenoidWindingResistance)
  seriesRLTimeConstantLaw :
    timeInSeconds setup.transientTimeConstant =
      inductanceInHenries setup.solenoidInductance /
        (resistanceInOhms setup.batteryInternalResistance +
          resistanceInOhms setup.externalResistorResistance +
          resistanceInOhms setup.solenoidWindingResistance)
  resistorVoltageTransient : ∀ t : ℝ, 0 ≤ t →
    voltageInVolts (setup.externalResistorVoltageAtSeconds t) =
      voltageInVolts setup.longTimeExternalResistorVoltage *
        (1 - Real.exp (-t / timeInSeconds setup.transientTimeConstant))
  longTimeMagneticEnergyLaw :
    energyInJoules setup.longTimeStoredMagneticEnergy =
      (1 / 2 : ℝ) * inductanceInHenries setup.solenoidInductance *
        currentInAmperes setup.longTimeSeriesCurrent ^ 2

/-! ## Derived circuit parameters -/

/-- The millisecond readout is one thousand times the SI-second readout. -/
lemma timeInMilliseconds_eq_thousand_mul_timeInSeconds
    (time : TimeQuantity) :
    timeInMilliseconds time = 1000 * timeInSeconds time := by
  have h := congrArg (fun value => (value.val : ℝ))
    (time.2
      ({UnitChoices.SI with time := TimeUnit.seconds} : UnitChoices)
      ({UnitChoices.SI with time := TimeUnit.milliseconds} : UnitChoices))
  change timeInMilliseconds time = _ * timeInSeconds time at h
  norm_num [UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.scale,
    TimeUnit.div_eq_val, TimeUnit.seconds, NNReal.smul_def] at h ⊢
  exact h

/-- The measured long-time resistor voltage and `50 Ω` label give `0.5 A`. -/
lemma longTimeSeriesCurrent_eq_halfAmpere
    (setup : SeriesSolenoidCircuit)
    (h_data : MatchesStatedMeasurements setup)
    (h_laws : SatisfiesIdealSeriesRLaws setup) :
    currentInAmperes setup.longTimeSeriesCurrent = 1 / 2 := by
  have h_ohm := h_laws.longTimeExternalResistorOhmsLaw
  rw [h_data.longTimeResistorVoltage, h_data.externalResistanceOhms] at h_ohm
  norm_num at h_ohm ⊢
  linarith

/-!
Because the resistor receives the full source voltage at long times, the
otherwise unknown solenoid winding resistance is inferred to vanish.
-/
lemma solenoidWindingResistance_eq_zeroOhms
    (setup : SeriesSolenoidCircuit)
    (h_data : MatchesStatedMeasurements setup)
    (h_laws : SatisfiesIdealSeriesRLaws setup) :
    resistanceInOhms setup.solenoidWindingResistance = 0 := by
  have h_current :=
    longTimeSeriesCurrent_eq_halfAmpere setup h_data h_laws
  have h_kirchhoff := h_laws.longTimeKirchhoffVoltageLaw
  rw [h_data.batteryVoltageVolts, h_data.negligibleBatteryInternalResistance,
    h_data.externalResistanceOhms, h_current] at h_kirchhoff
  norm_num at h_kirchhoff ⊢
  linarith

/-- The `8 ms` graph fit and `50 Ω` total resistance give `L = 0.4 H`. -/
lemma solenoidInductance_eq_twoFifthsHenry
    (setup : SeriesSolenoidCircuit)
    (h_data : MatchesStatedMeasurements setup)
    (h_graph : MatchesSuppliedVoltageTimeGraph setup)
    (h_laws : SatisfiesIdealSeriesRLaws setup) :
    inductanceInHenries setup.solenoidInductance = 2 / 5 := by
  have h_time_ms :
      timeInMilliseconds setup.transientTimeConstant = 8 := by
    rw [h_graph.fittedTimeConstantCalibratesPhysicalTime,
      h_graph.fittedTimeConstant]
  have h_time_seconds :
      timeInSeconds setup.transientTimeConstant = 1 / 125 := by
    have h_conversion :=
      timeInMilliseconds_eq_thousand_mul_timeInSeconds
        setup.transientTimeConstant
    rw [h_time_ms] at h_conversion
    norm_num at h_conversion ⊢
    linarith
  have h_winding :=
    solenoidWindingResistance_eq_zeroOhms setup h_data h_laws
  have h_time_constant := h_laws.seriesRLTimeConstantLaw
  rw [h_time_seconds, h_data.negligibleBatteryInternalResistance,
    h_data.externalResistanceOhms, h_winding] at h_time_constant
  norm_num at h_time_constant ⊢
  linarith

/-! ## Answer choices and target -/

/-- Labels of the four energies displayed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Energy in joules printed beside each answer label. -/
def displayedEnergyInJoules : AnswerChoice → ℝ
  | .A => 1 / 10
  | .B => 1 / 20
  | .C => 1 / 4
  | .D => 1 / 5

/-- The answer label recorded by the source dataset, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice exactly matches the independent stored-energy observable. -/
def MatchesLongTimeStoredEnergy
    (setup : SeriesSolenoidCircuit) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.longTimeStoredMagneticEnergy =
    displayedEnergyInJoules choice

/-- A choice is the unique exact match among the four displayed energies. -/
def IsUniqueMatchingAnswer
    (setup : SeriesSolenoidCircuit) (choice : AnswerChoice) : Prop :=
  MatchesLongTimeStoredEnergy setup choice ∧
    ∀ other : AnswerChoice,
      MatchesLongTimeStoredEnergy setup other → other = choice

/-!
At long times the current is `25 V / 50 Ω = 0.5 A`.  The graph's `8 ms`
time constant gives `L = τR = 0.4 H`, so `U = (1/2) L I² = 0.050 J`, the
unique displayed choice B.

This formalizes `thm:physics:phyx_mini_0989:target`.
-/
theorem problem_phyx_mini_0989
    (setup : SeriesSolenoidCircuit)
    (h_scenario : MatchesWrittenScenario setup)
    (h_data : MatchesStatedMeasurements setup)
    (h_graph : MatchesSuppliedVoltageTimeGraph setup)
    (h_physical : HasPhysicalSeriesRLParameters setup)
    (h_laws : SatisfiesIdealSeriesRLaws setup) :
    energyInJoules setup.longTimeStoredMagneticEnergy = 1 / 20 ∧
      IsUniqueMatchingAnswer setup .B := by
  have h_current :=
    longTimeSeriesCurrent_eq_halfAmpere setup h_data h_laws
  have h_inductance :=
    solenoidInductance_eq_twoFifthsHenry setup h_data h_graph h_laws
  have h_energy := h_laws.longTimeMagneticEnergyLaw
  rw [h_current, h_inductance] at h_energy
  norm_num at h_energy
  constructor
  · exact h_energy
  · constructor
    · simpa [MatchesLongTimeStoredEnergy, displayedEnergyInJoules] using h_energy
    · intro other h_other
      change energyInJoules setup.longTimeStoredMagneticEnergy =
        displayedEnergyInJoules other at h_other
      rw [h_energy] at h_other
      cases other with
      | A => norm_num [displayedEnergyInJoules] at h_other
      | B => rfl
      | C => norm_num [displayedEnergyInJoules] at h_other
      | D => norm_num [displayedEnergyInJoules] at h_other

end PhyXMiniProblems.ProblemPhyXMini0989
