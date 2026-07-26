import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0943

open Dimension

/-!
# Reactances and impedance of a measured series RLC circuit

The primary raster `943.png` shows one closed series loop containing a
variable-frequency AC source, a `500 Ω` resistor between nodes `a` and `b`, a
`0.40 mH` inductor between `b` and `c`, and a `100 pF` capacitor between `c`
and `d`.  An in-series ammeter reads `2.0 mA`.  RMS voltmeters read `1.0 V`
across the source terminals, `1.0 V` across `a-b`, `4.0 V` across `b-c`,
`4.0 V` across `c-d`, and `0 V` across the combined reactive pair `b-d`.

All physical component values and RMS observables are represented by
Physlib's unit-independent `Dimensionful (WithDim ...)` quantities.  Real
numbers occur only as coherent-SI readouts and as literal data printed in the
figure or answer choices.

Assumption/target split:

* governing laws: ideal-component identification, `X_L = ωL`,
  `X_C = 1/(ωC)`, the RMS laws `V_R = IR`, `V_L = I X_L`, and
  `V_C = I X_C`, reactive-voltage cancellation, the series-RLC impedance
  magnitude, and `V_s = I Z`;
* previous-part results: none;
* figure/data readouts: the four labelled nodes and series topology, every
  component value, the ammeter reading, and all five voltmeter readings;
* current target: `X_L = 2000 Ω`, `X_C = 2000 Ω`, and `Z = 500 Ω`.

The reactances and impedance are independent fields of the physical setup.
No premise or definition assigns them any of the requested numerical values.
-/

/-! ## Dimensionful electrical quantities and named-unit readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Resistance, reactance, and impedance have dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance has dimension resistance times time. -/
def electricalInductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- Capacitance has dimension charge per voltage. -/
def electricalCapacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- Angular frequency has inverse-time dimension; radians are dimensionless. -/
def angularFrequencyDimension : Dimension := T𝓭⁻¹

/-- A nonnegative, unit-independent RMS electric current. -/
abbrev RMSCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent RMS potential difference. -/
abbrev RMSVoltageQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative physical resistance, reactance, or impedance magnitude. -/
abbrev ResistanceMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent physical inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- A nonnegative, unit-independent physical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim electricalCapacitanceDimension NNReal)

/-- A nonnegative, unit-independent physical angular frequency. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim angularFrequencyDimension NNReal)

/-- Read any nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an RMS current in amperes. -/
def rmsCurrentInAmperes (current : RMSCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Read an RMS current in milliamperes. -/
def rmsCurrentInMilliamperes (current : RMSCurrentQuantity) : ℝ :=
  1000 * rmsCurrentInAmperes current

/-- Read an RMS potential difference in volts. -/
def rmsVoltageInVolts (voltage : RMSVoltageQuantity) : ℝ :=
  nonnegativeSIReadout voltage

/-- Read a resistance, reactance, or impedance magnitude in ohms. -/
def resistanceMagnitudeInOhms
    (quantity : ResistanceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout quantity

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read an inductance in millihenries. -/
def inductanceInMillihenries (inductance : InductanceQuantity) : ℝ :=
  1000 * inductanceInHenries inductance

/-- Read a capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read a capacitance in picofarads. -/
def capacitanceInPicofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 12 * capacitanceInFarads capacitance

/-- Read angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-! ## Circuit roles, labelled geometry, and measured observables -/

/-- The four electrically distinct junctions labelled in the raster. -/
inductive CircuitNode where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- The four elements encountered in one traversal of the closed loop. -/
inductive CircuitElement where
  | acSource
  | resistor
  | inductor
  | capacitor
  deriving DecidableEq, Fintype, Repr

/-- Idealized physical roles assigned to the standard circuit symbols. -/
inductive ComponentModel where
  | variableFrequencyACSource
  | idealOhmicResistor
  | idealInductor
  | idealCapacitor
  | other
  deriving DecidableEq, Repr

/-- The five voltmeter placements visible in image `943.png`. -/
inductive VoltageMeterPlacement where
  | sourceAD
  | resistorAB
  | inductorBC
  | capacitorCD
  | reactivePairBD
  deriving DecidableEq, Fintype, Repr

/-- Literal topology and scalar annotations transcribed from the raster. -/
structure SeriesRLCFigure where
  componentSymbolShown : CircuitElement → Bool
  nodeLabelShown : CircuitNode → Bool
  voltageMeterShown : VoltageMeterPlacement → Bool
  elementTerminals : CircuitElement → CircuitNode × CircuitNode
  voltageMeterTerminals :
    VoltageMeterPlacement → CircuitNode × CircuitNode
  seriesOrderFromNodeA : List CircuitElement
  formsSingleClosedLoop : Bool
  sourceSymbolShowsAlternatingWave : Bool
  ammeterShownInSeries : Bool
  printedRMSCurrentInMilliamperes : ℝ
  printedRMSVoltageInVolts : VoltageMeterPlacement → ℝ
  printedResistanceInOhms : ℝ
  printedInductanceInMillihenries : ℝ
  printedCapacitanceInPicofarads : ℝ

/-- The variable-frequency source with its independent terminal observable. -/
structure VariableFrequencyACSource where
  driveAngularFrequency : AngularFrequencyQuantity
  rmsTerminalVoltage : RMSVoltageQuantity

/-!
Independent physical data for the measured series RLC circuit.  In particular,
the reactance and impedance fields are observables constrained later by
constitutive and circuit laws; they are not definitions made from the answer.
-/
structure SeriesRLCSetup where
  source : VariableFrequencyACSource
  componentModel : CircuitElement → ComponentModel
  resistance : ResistanceMagnitudeQuantity
  inductance : InductanceQuantity
  capacitance : CapacitanceQuantity
  seriesRMSCurrent : RMSCurrentQuantity
  inductiveReactance : ResistanceMagnitudeQuantity
  capacitiveReactance : ResistanceMagnitudeQuantity
  seriesImpedanceMagnitude : ResistanceMagnitudeQuantity
  meteredRMSVoltage : VoltageMeterPlacement → RMSVoltageQuantity
  figure : SeriesRLCFigure

/-! ## Scenario assumptions and primary-figure readouts -/

/-- The standard ideal lumped-component interpretation of the shown symbols. -/
structure MatchesIdealVariableFrequencySeriesRLCScenario
    (setup : SeriesRLCSetup) : Prop where
  sourceModel :
    setup.componentModel .acSource = .variableFrequencyACSource
  resistorModel :
    setup.componentModel .resistor = .idealOhmicResistor
  inductorModel :
    setup.componentModel .inductor = .idealInductor
  capacitorModel :
    setup.componentModel .capacitor = .idealCapacitor

/-!
Primary-image evidence and calibration.  The circle marked `2.0 mA` is treated
as an in-series ammeter, while the five blue circles are RMS voltmeters across
the node pairs indicated by their fields.
-/
structure MatchesSuppliedSeriesRLCFigure (setup : SeriesRLCSetup) : Prop where
  everyComponentSymbolShown : ∀ element,
    setup.figure.componentSymbolShown element = true
  everyNodeLabelShown : ∀ node,
    setup.figure.nodeLabelShown node = true
  everyVoltageMeterShown : ∀ meter,
    setup.figure.voltageMeterShown meter = true
  resistorTerminals :
    setup.figure.elementTerminals .resistor = (.a, .b)
  inductorTerminals :
    setup.figure.elementTerminals .inductor = (.b, .c)
  capacitorTerminals :
    setup.figure.elementTerminals .capacitor = (.c, .d)
  sourceTerminals :
    setup.figure.elementTerminals .acSource = (.d, .a)
  sourceMeterTerminals :
    setup.figure.voltageMeterTerminals .sourceAD = (.a, .d)
  resistorMeterTerminals :
    setup.figure.voltageMeterTerminals .resistorAB = (.a, .b)
  inductorMeterTerminals :
    setup.figure.voltageMeterTerminals .inductorBC = (.b, .c)
  capacitorMeterTerminals :
    setup.figure.voltageMeterTerminals .capacitorCD = (.c, .d)
  reactivePairMeterTerminals :
    setup.figure.voltageMeterTerminals .reactivePairBD = (.b, .d)
  seriesTraversal :
    setup.figure.seriesOrderFromNodeA =
      [.resistor, .inductor, .capacitor, .acSource]
  singleClosedLoop : setup.figure.formsSingleClosedLoop = true
  alternatingSourceSymbol :
    setup.figure.sourceSymbolShowsAlternatingWave = true
  ammeterInSeries : setup.figure.ammeterShownInSeries = true
  printedCurrent : setup.figure.printedRMSCurrentInMilliamperes = 2
  printedSourceVoltage :
    setup.figure.printedRMSVoltageInVolts .sourceAD = 1
  printedResistorVoltage :
    setup.figure.printedRMSVoltageInVolts .resistorAB = 1
  printedInductorVoltage :
    setup.figure.printedRMSVoltageInVolts .inductorBC = 4
  printedCapacitorVoltage :
    setup.figure.printedRMSVoltageInVolts .capacitorCD = 4
  printedReactivePairVoltage :
    setup.figure.printedRMSVoltageInVolts .reactivePairBD = 0
  printedResistance : setup.figure.printedResistanceInOhms = 500
  printedInductance :
    setup.figure.printedInductanceInMillihenries = 2 / 5
  printedCapacitance : setup.figure.printedCapacitanceInPicofarads = 100
  currentCalibration :
    rmsCurrentInMilliamperes setup.seriesRMSCurrent =
      setup.figure.printedRMSCurrentInMilliamperes
  sourceTerminalVoltageCalibration :
    rmsVoltageInVolts setup.source.rmsTerminalVoltage =
      setup.figure.printedRMSVoltageInVolts .sourceAD
  sourceMeterCalibration :
    rmsVoltageInVolts (setup.meteredRMSVoltage .sourceAD) =
      setup.figure.printedRMSVoltageInVolts .sourceAD
  resistorMeterCalibration :
    rmsVoltageInVolts (setup.meteredRMSVoltage .resistorAB) =
      setup.figure.printedRMSVoltageInVolts .resistorAB
  inductorMeterCalibration :
    rmsVoltageInVolts (setup.meteredRMSVoltage .inductorBC) =
      setup.figure.printedRMSVoltageInVolts .inductorBC
  capacitorMeterCalibration :
    rmsVoltageInVolts (setup.meteredRMSVoltage .capacitorCD) =
      setup.figure.printedRMSVoltageInVolts .capacitorCD
  reactivePairMeterCalibration :
    rmsVoltageInVolts (setup.meteredRMSVoltage .reactivePairBD) =
      setup.figure.printedRMSVoltageInVolts .reactivePairBD
  resistanceCalibration :
    resistanceMagnitudeInOhms setup.resistance =
      setup.figure.printedResistanceInOhms
  inductanceCalibration :
    inductanceInMillihenries setup.inductance =
      setup.figure.printedInductanceInMillihenries
  capacitanceCalibration :
    capacitanceInPicofarads setup.capacitance =
      setup.figure.printedCapacitanceInPicofarads

/-! ## Governing physical laws -/

/-- Positivity and nondegeneracy of the driven passive circuit. -/
structure HasPhysicalSeriesRLCParameters (setup : SeriesRLCSetup) : Prop where
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.source.driveAngularFrequency
  currentPositive : 0 < rmsCurrentInAmperes setup.seriesRMSCurrent
  resistancePositive : 0 < resistanceMagnitudeInOhms setup.resistance
  inductancePositive : 0 < inductanceInHenries setup.inductance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  inductiveReactancePositive :
    0 < resistanceMagnitudeInOhms setup.inductiveReactance
  capacitiveReactancePositive :
    0 < resistanceMagnitudeInOhms setup.capacitiveReactance
  impedanceMagnitudePositive :
    0 < resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude

/-!
Standard sinusoidal steady-state laws for an ideal series RLC circuit.  These
are general relations among independently supplied physical observables and
contain none of the requested numerical reactance or impedance values.
-/
structure SatisfiesIdealSeriesRLCSteadyStateLaws
    (setup : SeriesRLCSetup) : Prop where
  inductiveReactanceLaw :
    resistanceMagnitudeInOhms setup.inductiveReactance =
      angularFrequencyInRadiansPerSecond setup.source.driveAngularFrequency *
        inductanceInHenries setup.inductance
  capacitiveReactanceLaw :
    resistanceMagnitudeInOhms setup.capacitiveReactance =
      1 /
        (angularFrequencyInRadiansPerSecond
            setup.source.driveAngularFrequency *
          capacitanceInFarads setup.capacitance)
  resistorRMSVoltageLaw :
    rmsVoltageInVolts (setup.meteredRMSVoltage .resistorAB) =
      rmsCurrentInAmperes setup.seriesRMSCurrent *
        resistanceMagnitudeInOhms setup.resistance
  inductorRMSVoltageLaw :
    rmsVoltageInVolts (setup.meteredRMSVoltage .inductorBC) =
      rmsCurrentInAmperes setup.seriesRMSCurrent *
        resistanceMagnitudeInOhms setup.inductiveReactance
  capacitorRMSVoltageLaw :
    rmsVoltageInVolts (setup.meteredRMSVoltage .capacitorCD) =
      rmsCurrentInAmperes setup.seriesRMSCurrent *
        resistanceMagnitudeInOhms setup.capacitiveReactance
  reactivePairRMSVoltageLaw :
    rmsVoltageInVolts (setup.meteredRMSVoltage .reactivePairBD) =
      rmsCurrentInAmperes setup.seriesRMSCurrent *
        |resistanceMagnitudeInOhms setup.inductiveReactance -
          resistanceMagnitudeInOhms setup.capacitiveReactance|
  seriesImpedanceMagnitudeLaw :
    resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude =
      Real.sqrt
        (resistanceMagnitudeInOhms setup.resistance ^ 2 +
          (resistanceMagnitudeInOhms setup.inductiveReactance -
            resistanceMagnitudeInOhms setup.capacitiveReactance) ^ 2)
  sourceRMSVoltageLaw :
    rmsVoltageInVolts setup.source.rmsTerminalVoltage =
      rmsCurrentInAmperes setup.seriesRMSCurrent *
        resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude

/-! ## Displayed answer choices and requested conclusion -/

/-- Labels of the four resistance-valued choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The resistance or reactance magnitude printed beside each choice, in ohms. -/
def AnswerChoice.displayedMagnitudeInOhms : AnswerChoice → ℝ
  | .A => 200
  | .B => 2000
  | .C => 1000
  | .D => 2200

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Blueprint label: `thm:physics:phyx_mini_0943:target`.

The `4.0 V` component readings at `2.0 mA` give equal inductive and
capacitive reactances of `2000 Ω`, which is displayed choice B.  Their phasor
contributions cancel, and the `1.0 V` source reading at the same current gives
the series impedance magnitude `500 Ω`.
-/
theorem problem_phyx_mini_0943
    (setup : SeriesRLCSetup)
    (_scenario : MatchesIdealVariableFrequencySeriesRLCScenario setup)
    (_figure : MatchesSuppliedSeriesRLCFigure setup)
    (_physical : HasPhysicalSeriesRLCParameters setup)
    (_laws : SatisfiesIdealSeriesRLCSteadyStateLaws setup) :
    resistanceMagnitudeInOhms setup.inductiveReactance =
        recordedDatasetAnswer.displayedMagnitudeInOhms ∧
      resistanceMagnitudeInOhms setup.capacitiveReactance =
        recordedDatasetAnswer.displayedMagnitudeInOhms ∧
      resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude = 500 := by
  have hcurrentMilliampere :
      rmsCurrentInMilliamperes setup.seriesRMSCurrent = 2 := by
    rw [_figure.currentCalibration, _figure.printedCurrent]
  have hcurrentAmpere :
      rmsCurrentInAmperes setup.seriesRMSCurrent = 1 / 500 := by
    unfold rmsCurrentInMilliamperes at hcurrentMilliampere
    nlinarith
  have hinductorVoltage :
      rmsVoltageInVolts (setup.meteredRMSVoltage .inductorBC) = 4 := by
    rw [_figure.inductorMeterCalibration, _figure.printedInductorVoltage]
  have hcapacitorVoltage :
      rmsVoltageInVolts (setup.meteredRMSVoltage .capacitorCD) = 4 := by
    rw [_figure.capacitorMeterCalibration, _figure.printedCapacitorVoltage]
  have hsourceVoltage :
      rmsVoltageInVolts setup.source.rmsTerminalVoltage = 1 := by
    rw [_figure.sourceTerminalVoltageCalibration, _figure.printedSourceVoltage]
  have hinductiveReactance :
      resistanceMagnitudeInOhms setup.inductiveReactance = 2000 := by
    have hInductorLaw := _laws.inductorRMSVoltageLaw
    rw [hinductorVoltage, hcurrentAmpere] at hInductorLaw
    nlinarith [hInductorLaw]
  have hcapacitiveReactance :
      resistanceMagnitudeInOhms setup.capacitiveReactance = 2000 := by
    have hCapacitorLaw := _laws.capacitorRMSVoltageLaw
    rw [hcapacitorVoltage, hcurrentAmpere] at hCapacitorLaw
    nlinarith [hCapacitorLaw]
  have himpedance :
      resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude = 500 := by
    have hSourceLaw := _laws.sourceRMSVoltageLaw
    rw [hsourceVoltage, hcurrentAmpere] at hSourceLaw
    nlinarith [hSourceLaw]
  simpa [recordedDatasetAnswer, AnswerChoice.displayedMagnitudeInOhms] using
    And.intro hinductiveReactance (And.intro hcapacitiveReactance himpedance)

end PhyXMiniProblems.ProblemPhyXMini0943
