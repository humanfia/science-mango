import Mathlib
import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0988

open Dimension Filter

/-!
# Winding resistance of a solenoid from a switched series-RL experiment

A solenoid, a `10.0 Ω` external resistor, a battery with negligible internal
resistance, and a switch form one series circuit.  An ideal voltmeter records
the voltage `v_L` across the whole solenoid after the switch closes.  Thus the
measured solenoid voltage contains both the winding's resistive drop and the
self-inductive drop.

We choose seconds as the coordinate unit of Physlib's `Time`.  Electrical
quantities are unit-independent Physlib `Dimensionful` values; real numbers
occur only as coherent-SI readouts, literal plot coordinates, and displayed
answer values.

Assumption/target split:

* governing laws: Ohm's law for both resistances, `v_ind = L di/dt`, addition
  of the solenoid's winding and inductive voltage drops, Kirchhoff's loop law,
  and zero current drawn by the ideal voltmeter;
* previous-state results: current is zero immediately after closing, while in
  the long-time regime its derivative is zero; the named regime observables
  agree with the transient waveforms and their long-time limits;
* figure/data readouts: external resistance `10.0 Ω`, solenoid voltage `50.0 V`
  immediately after closing and `20.0 V` after a long time, plus the primary
  raster's `t`-in-ms and `v_L`-in-V axes, bounds, grid, and decreasing black
  data points;
* current target conclusions: the winding resistance is exactly `20/3 Ω`, and
  the uniquely closest displayed value is `6.67 Ω`, recorded choice B.

Neither the exact winding resistance nor choice B occurs in a premise below.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has physical dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance has physical dimension voltage times time per current. -/
def inductanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * electricCurrentDimension⁻¹

/-- Current change rate has physical dimension current per time. -/
def electricCurrentRateDimension : Dimension :=
  electricCurrentDimension * T𝓭⁻¹

/-- A signed, unit-independent electric potential difference. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, unit-independent electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent current change rate. -/
abbrev ElectricCurrentRateQuantity : Type :=
  Dimensionful (WithDim electricCurrentRateDimension ℝ)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent self-inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an oriented potential difference in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  signedSIReadout potentialDifference

/-- Read an oriented current in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Read an oriented current change rate in amperes per second. -/
def currentRateInAmperesPerSecond
    (currentRate : ElectricCurrentRateQuantity) : ℝ :=
  signedSIReadout currentRate

/-- Read resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read self-inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeSIReadout inductance

/-! ## Apparatus roles and primary-plot labels -/

/-- Components explicitly named in the measurement setup. -/
inductive CircuitComponent where
  | battery
  | switch
  | externalResistor
  | solenoid
  | voltmeter
  deriving DecidableEq, Fintype, Repr

/-- Idealized physical roles assigned to the named components. -/
inductive ComponentModel where
  | idealVoltageSourceNegligibleInternalResistance
  | idealSwitch
  | idealOhmicResistor
  | windingResistanceInSeriesWithSelfInductance
  | idealInfiniteInputResistanceVoltmeter
  deriving DecidableEq, Repr

/-- The topology stated in the prose, including the voltmeter connection. -/
inductive CircuitTopology where
  | batterySwitchResistorSolenoidSeriesVoltmeterAcrossSolenoid
  deriving DecidableEq, Repr

/-- The two switch states needed for the closing experiment. -/
inductive SwitchPosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Named limiting regimes used by the two additional voltage measurements. -/
inductive TransientRegime where
  | immediatelyAfterClosing
  | longAfterClosing
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity attached to a graph axis. -/
inductive PlotQuantity where
  | elapsedTime
  | solenoidTerminalVoltage
  deriving DecidableEq, Repr

/-- Units explicitly printed beside the axes of the supplied raster. -/
inductive PlotUnit where
  | millisecond
  | volt
  deriving DecidableEq, Repr

/-- Visual rendering of each experimental sample. -/
inductive MarkerColor where
  | black
  deriving DecidableEq, Repr

/-- Marker shape visible in the primary raster. -/
inductive MarkerShape where
  | filledDot
  deriving DecidableEq, Repr

/-- Qualitative shape read from the plotted experimental samples. -/
inductive CurveAppearance where
  | decreasingTowardPositiveAsymptote
  deriving DecidableEq, Repr

/-!
Literal content of image `988.png`.  The sample-time set and voltage readout
retain the plotted data separately from the continuous physical waveform.
-/
structure SolenoidVoltagePlot where
  horizontalAxisQuantity : PlotQuantity
  verticalAxisQuantity : PlotQuantity
  horizontalAxisUnit : PlotUnit
  verticalAxisUnit : PlotUnit
  horizontalMinimum : ℝ
  horizontalMaximum : ℝ
  verticalMinimum : ℝ
  verticalMaximum : ℝ
  sampleTimesMilliseconds : Set ℝ
  plottedVoltageVolts : ℝ → ℝ
  markerColor : MarkerColor
  markerShape : MarkerShape
  rectangularGridShown : Bool
  curveAppearance : CurveAppearance

/-!
Independent physical observables of the switched circuit.  The solenoid
winding resistance is a field, not a definition of the requested answer.
-/
structure SolenoidSeriesCircuitSetup where
  componentModel : CircuitComponent → ComponentModel
  topology : CircuitTopology
  switchPosition : Time → SwitchPosition
  batteryVoltage : PotentialDifferenceQuantity
  externalResistorResistance : ResistanceQuantity
  solenoidWindingResistance : ResistanceQuantity
  solenoidSelfInductance : InductanceQuantity
  currentWaveform : Time → ElectricCurrentQuantity
  solenoidTerminalVoltageWaveform : Time → PotentialDifferenceQuantity
  currentAtRegime : TransientRegime → ElectricCurrentQuantity
  currentRateAtRegime : TransientRegime → ElectricCurrentRateQuantity
  externalResistorVoltageDropAtRegime :
    TransientRegime → PotentialDifferenceQuantity
  solenoidWindingVoltageDropAtRegime :
    TransientRegime → PotentialDifferenceQuantity
  solenoidInductiveVoltageDropAtRegime :
    TransientRegime → PotentialDifferenceQuantity
  solenoidTerminalVoltageAtRegime :
    TransientRegime → PotentialDifferenceQuantity
  voltmeterCurrentAtRegime : TransientRegime → ElectricCurrentQuantity
  figure : SolenoidVoltagePlot

/-- The circuit-current readout as a function of time in seconds. -/
def currentWaveformInAmperes
    (setup : SolenoidSeriesCircuitSetup) : Time → ℝ :=
  fun time => currentInAmperes (setup.currentWaveform time)

/-- Time derivative of the current readout, in amperes per second. -/
def currentDerivativeInAmperesPerSecond
    (setup : SolenoidSeriesCircuitSetup) : Time → ℝ :=
  Time.deriv (currentWaveformInAmperes setup)

/-- The solenoid terminal-voltage readout as a function of time in seconds. -/
def solenoidVoltageWaveformInVolts
    (setup : SolenoidSeriesCircuitSetup) : Time → ℝ :=
  fun time =>
    potentialDifferenceInVolts (setup.solenoidTerminalVoltageWaveform time)

/-- Evaluate the continuous voltage waveform at a plot coordinate in milliseconds. -/
def solenoidVoltageAtMillisecondsInVolts
    (setup : SolenoidSeriesCircuitSetup) (elapsedMilliseconds : ℝ) : ℝ :=
  solenoidVoltageWaveformInVolts setup
    (((elapsedMilliseconds / 1000 : ℝ)) : Time)

/-! ## Scenario, raster evidence, measured data, and governing laws -/

/-- The idealized apparatus and series connection stated in the problem. -/
structure MatchesSolenoidSeriesCircuitScenario
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  batteryModel :
    setup.componentModel .battery =
      .idealVoltageSourceNegligibleInternalResistance
  switchModel : setup.componentModel .switch = .idealSwitch
  externalResistorModel :
    setup.componentModel .externalResistor = .idealOhmicResistor
  solenoidModel :
    setup.componentModel .solenoid =
      .windingResistanceInSeriesWithSelfInductance
  voltmeterModel :
    setup.componentModel .voltmeter =
      .idealInfiniteInputResistanceVoltmeter
  statedTopology :
    setup.topology =
      .batterySwitchResistorSolenoidSeriesVoltmeterAcrossSolenoid
  switchOpenBeforeClosure : ∀ time : Time, time < 0 →
    setup.switchPosition time = .open
  switchClosedFromTimeZero : ∀ time : Time, 0 ≤ time →
    setup.switchPosition time = .closed

/-!
Primary-raster evidence: the axis labels and scales, grid, black dots, their
decreasing order, and calibration against the measured voltage waveform.
The image itself contains no resistance value or answer label.
-/
structure MatchesPrimarySolenoidVoltagePlot
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  horizontalAxisIsTime :
    setup.figure.horizontalAxisQuantity = .elapsedTime
  verticalAxisIsSolenoidVoltage :
    setup.figure.verticalAxisQuantity = .solenoidTerminalVoltage
  timeAxisUsesMilliseconds :
    setup.figure.horizontalAxisUnit = .millisecond
  voltageAxisUsesVolts : setup.figure.verticalAxisUnit = .volt
  timeAxisMinimum : setup.figure.horizontalMinimum = 0
  timeAxisMaximum : setup.figure.horizontalMaximum = 4.5
  voltageAxisMinimum : setup.figure.verticalMinimum = 20
  voltageAxisMaximum : setup.figure.verticalMaximum = 45
  blackMarkers : setup.figure.markerColor = .black
  filledDotMarkers : setup.figure.markerShape = .filledDot
  gridShown : setup.figure.rectangularGridShown = true
  displayedShape :
    setup.figure.curveAppearance = .decreasingTowardPositiveAsymptote
  samplesNonempty : setup.figure.sampleTimesMilliseconds.Nonempty
  sampleTimesWithinAxes : ∀ time,
    time ∈ setup.figure.sampleTimesMilliseconds →
      setup.figure.horizontalMinimum ≤ time ∧
        time ≤ setup.figure.horizontalMaximum
  sampleVoltagesWithinAxes : ∀ time,
    time ∈ setup.figure.sampleTimesMilliseconds →
      setup.figure.verticalMinimum ≤ setup.figure.plottedVoltageVolts time ∧
        setup.figure.plottedVoltageVolts time ≤ setup.figure.verticalMaximum
  samplesStrictlyDecrease : ∀ time₁ time₂,
    time₁ ∈ setup.figure.sampleTimesMilliseconds →
      time₂ ∈ setup.figure.sampleTimesMilliseconds →
        time₁ < time₂ →
          setup.figure.plottedVoltageVolts time₂ <
            setup.figure.plottedVoltageVolts time₁
  samplesCalibrateWaveform : ∀ time,
    time ∈ setup.figure.sampleTimesMilliseconds →
      setup.figure.plottedVoltageVolts time =
        solenoidVoltageAtMillisecondsInVolts setup time

/-!
The three numerical measurements stated in the prose.  They calibrate an
external component and two independently stored voltage observables; no
solenoid winding resistance is asserted here.
-/
structure HasStatedSolenoidCircuitMeasurements
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  externalResistanceIsTenOhms :
    resistanceInOhms setup.externalResistorResistance = 10
  solenoidVoltageImmediatelyAfterClosingIsFiftyVolts :
    potentialDifferenceInVolts
      (setup.solenoidTerminalVoltageAtRegime .immediatelyAfterClosing) = 50
  solenoidVoltageLongAfterClosingIsTwentyVolts :
    potentialDifferenceInVolts
      (setup.solenoidTerminalVoltageAtRegime .longAfterClosing) = 20

/-- Positivity and nondegeneracy of the physical circuit parameters. -/
structure HasPhysicalSolenoidCircuitParameters
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  batteryVoltagePositive :
    0 < potentialDifferenceInVolts setup.batteryVoltage
  externalResistancePositive :
    0 < resistanceInOhms setup.externalResistorResistance
  windingResistancePositive :
    0 < resistanceInOhms setup.solenoidWindingResistance
  selfInductancePositive :
    0 < inductanceInHenries setup.solenoidSelfInductance

/-!
The initial and limiting meanings of the two named regimes.  The initially
uncharged inductor current is continuous and hence zero at closure.  At long
times current has settled, so its derivative tends to the stored zero rate.
These are previous-state/steady-state facts, not the requested resistance.
-/
structure HasClosingAndLongTimeRegimes
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  currentImmediatelyAfterClosingIsZero :
    currentInAmperes
      (setup.currentAtRegime .immediatelyAfterClosing) = 0
  immediateCurrentMatchesWaveform :
    currentInAmperes
      (setup.currentAtRegime .immediatelyAfterClosing) =
        currentWaveformInAmperes setup 0
  immediateCurrentRateMatchesWaveform :
    currentRateInAmperesPerSecond
      (setup.currentRateAtRegime .immediatelyAfterClosing) =
        currentDerivativeInAmperesPerSecond setup 0
  immediateVoltageMatchesWaveform :
    potentialDifferenceInVolts
      (setup.solenoidTerminalVoltageAtRegime .immediatelyAfterClosing) =
        solenoidVoltageWaveformInVolts setup 0
  longTimeCurrentConverges :
    Tendsto (currentWaveformInAmperes setup) atTop
      (nhds
        (currentInAmperes
          (setup.currentAtRegime .longAfterClosing)))
  longTimeCurrentDerivativeConverges :
    Tendsto (currentDerivativeInAmperesPerSecond setup) atTop
      (nhds
        (currentRateInAmperesPerSecond
          (setup.currentRateAtRegime .longAfterClosing)))
  longTimeCurrentRateIsZero :
    currentRateInAmperesPerSecond
      (setup.currentRateAtRegime .longAfterClosing) = 0
  longTimeVoltageConverges :
    Tendsto (solenoidVoltageWaveformInVolts setup) atTop
      (nhds
        (potentialDifferenceInVolts
          (setup.solenoidTerminalVoltageAtRegime .longAfterClosing)))

/-!
Lumped-element laws in each named regime.  The measured solenoid terminal
voltage is the sum of winding and self-inductive drops.  All equalities relate
independent observables and none fixes the winding resistance numerically.
-/
structure SatisfiesSeriesRLSolenoidLaws
    (setup : SolenoidSeriesCircuitSetup) : Prop where
  idealVoltmeterDrawsNoCurrent : ∀ regime,
    currentInAmperes (setup.voltmeterCurrentAtRegime regime) = 0
  externalResistorOhmLaw : ∀ regime,
    potentialDifferenceInVolts
        (setup.externalResistorVoltageDropAtRegime regime) =
      resistanceInOhms setup.externalResistorResistance *
        currentInAmperes (setup.currentAtRegime regime)
  solenoidWindingOhmLaw : ∀ regime,
    potentialDifferenceInVolts
        (setup.solenoidWindingVoltageDropAtRegime regime) =
      resistanceInOhms setup.solenoidWindingResistance *
        currentInAmperes (setup.currentAtRegime regime)
  solenoidInductiveVoltageLaw : ∀ regime,
    potentialDifferenceInVolts
        (setup.solenoidInductiveVoltageDropAtRegime regime) =
      inductanceInHenries setup.solenoidSelfInductance *
        currentRateInAmperesPerSecond (setup.currentRateAtRegime regime)
  solenoidTerminalVoltageComposition : ∀ regime,
    potentialDifferenceInVolts
        (setup.solenoidTerminalVoltageAtRegime regime) =
      potentialDifferenceInVolts
          (setup.solenoidWindingVoltageDropAtRegime regime) +
        potentialDifferenceInVolts
          (setup.solenoidInductiveVoltageDropAtRegime regime)
  kirchhoffLoopLaw : ∀ regime,
    potentialDifferenceInVolts setup.batteryVoltage =
      potentialDifferenceInVolts
          (setup.externalResistorVoltageDropAtRegime regime) +
        potentialDifferenceInVolts
          (setup.solenoidTerminalVoltageAtRegime regime)

/-! ## Displayed choices and final target -/

/-- Labels of the four resistance choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed resistance values, interpreted in ohms. -/
def AnswerChoice.displayedResistanceInOhms : AnswerChoice → ℝ
  | .A => 10.0
  | .B => 6.67
  | .C => 3.33
  | .D => 13.3

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A displayed decimal choice is correct when it is strictly closer to the exact
winding resistance than every other displayed value.
-/
def IsUniqueClosestSolenoidResistanceChoice
    (setup : SolenoidSeriesCircuitSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |resistanceInOhms setup.solenoidWindingResistance -
        choice.displayedResistanceInOhms| <
      |resistanceInOhms setup.solenoidWindingResistance -
        other.displayedResistanceInOhms|

/-!
At closure the zero current makes the external resistor drop zero, so the
`50 V` solenoid reading is also the battery voltage.  At steady state the
inductive drop is zero.  KVL and the `20 V` solenoid reading give a current of
`(50 - 20) / 10 = 3 A`; winding Ohm's law then gives
`R_L = 20 / 3 Ω`.  Consequently `6.67 Ω` is the uniquely closest displayed
answer, choice B.

Blueprint label: `thm:physics:phyx_mini_0988:target`.
-/
theorem solenoid_winding_resistance_eq_twenty_div_three_ohms
    (setup : SolenoidSeriesCircuitSetup)
    (_scenario : MatchesSolenoidSeriesCircuitScenario setup)
    (_figure : MatchesPrimarySolenoidVoltagePlot setup)
    (_measurements : HasStatedSolenoidCircuitMeasurements setup)
    (_physical : HasPhysicalSolenoidCircuitParameters setup)
    (_regimes : HasClosingAndLongTimeRegimes setup)
    (_laws : SatisfiesSeriesRLSolenoidLaws setup) :
    resistanceInOhms setup.solenoidWindingResistance = (20 : ℝ) / 3 ∧
      IsUniqueClosestSolenoidResistanceChoice setup recordedDatasetAnswer := by
  have hImmediateCurrent :
      currentInAmperes
          (setup.currentAtRegime .immediatelyAfterClosing) = 0 :=
    _regimes.currentImmediatelyAfterClosingIsZero
  have hImmediateExternalDrop :
      potentialDifferenceInVolts
          (setup.externalResistorVoltageDropAtRegime
            .immediatelyAfterClosing) = 0 := by
    rw [_laws.externalResistorOhmLaw, hImmediateCurrent, mul_zero]
  have hBatteryVoltage :
      potentialDifferenceInVolts setup.batteryVoltage = 50 := by
    have hKVL := _laws.kirchhoffLoopLaw .immediatelyAfterClosing
    have hSolenoid :=
      _measurements.solenoidVoltageImmediatelyAfterClosingIsFiftyVolts
    linarith

  have hLongRate :
      currentRateInAmperesPerSecond
          (setup.currentRateAtRegime .longAfterClosing) = 0 :=
    _regimes.longTimeCurrentRateIsZero
  have hLongInductiveDrop :
      potentialDifferenceInVolts
          (setup.solenoidInductiveVoltageDropAtRegime
            .longAfterClosing) = 0 := by
    rw [_laws.solenoidInductiveVoltageLaw, hLongRate, mul_zero]
  have hLongWindingDrop :
      potentialDifferenceInVolts
          (setup.solenoidWindingVoltageDropAtRegime
            .longAfterClosing) = 20 := by
    have hComposition :=
      _laws.solenoidTerminalVoltageComposition .longAfterClosing
    have hSolenoid :=
      _measurements.solenoidVoltageLongAfterClosingIsTwentyVolts
    linarith
  have hLongExternalDrop :
      potentialDifferenceInVolts
          (setup.externalResistorVoltageDropAtRegime
            .longAfterClosing) = 30 := by
    have hKVL := _laws.kirchhoffLoopLaw .longAfterClosing
    have hSolenoid :=
      _measurements.solenoidVoltageLongAfterClosingIsTwentyVolts
    linarith
  have hLongCurrent :
      currentInAmperes (setup.currentAtRegime .longAfterClosing) = 3 := by
    have hOhm := _laws.externalResistorOhmLaw .longAfterClosing
    have hResistance := _measurements.externalResistanceIsTenOhms
    nlinarith
  have hWindingResistance :
      resistanceInOhms setup.solenoidWindingResistance = (20 : ℝ) / 3 := by
    have hOhm := _laws.solenoidWindingOhmLaw .longAfterClosing
    nlinarith

  constructor
  · exact hWindingResistance
  · rw [IsUniqueClosestSolenoidResistanceChoice, hWindingResistance]
    intro other hOther
    fin_cases other
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedResistanceInOhms]
    · exact (hOther rfl).elim
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedResistanceInOhms]
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedResistanceInOhms]

end PhyXMiniProblems.ProblemPhyXMini0988
