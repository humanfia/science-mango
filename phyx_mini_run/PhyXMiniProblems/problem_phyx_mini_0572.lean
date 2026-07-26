import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0572

open Dimension

/-!
# Forward-biased diode in a series circuit

The primary figure shows one closed loop containing a constant-voltage source,
a forward-biased diode, and a resistor labelled `R`.  The prose gives the
diode's reverse-current magnitude as `1.0 * 10^-5 A`, while the source is
labelled `6 volts`.  The voltage-valued answer choices and recorded answer show
that the recoverable target is the voltage drop across `R`.

The source's sentence about a photon wavelength and an `l = 0` to `l = 1`
transition is incompatible with both the circuit figure and every answer
choice.  No atomic-system data from which such a wavelength could be inferred
is supplied, so that corrupted sentence is not represented as a second target.

Physical current, potential difference, and resistance are represented by
unit-independent Physlib quantities.  Real numbers occur only as calibrated SI
readouts and printed answer-choice values.
-/

/-! ## Dimensionful electrical quantities and SI readouts -/

/-- Electric current has the physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential has the physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has the physical dimension potential per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent magnitude of electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnitude of potential difference. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Read a potential-difference magnitude in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  nonnegativeSIReadout potential

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-! ## Physical components and labels visible in the primary figure -/

/-- Coarse material classes used by the textbook diode model. -/
inductive DiodeMaterial where
  | germanium
  | silicon
  | other
  deriving DecidableEq, Repr

/-- The bias orientation in which the diode is connected. -/
inductive DiodeBias where
  | forward
  | reverse
  deriving DecidableEq, Repr

/-- The same physical diode in its preliminary reverse-current measurement and circuit use. -/
structure Diode where
  reverseBiasCurrent : ElectricCurrentQuantity
  forwardVoltageDrop : ElectricPotentialQuantity
  material : DiodeMaterial

/-- The resistor marked `R` in the figure. -/
structure Resistor where
  printedLabel : String
  resistance : ElectricalResistanceQuantity
  voltageDrop : ElectricPotentialQuantity

/-- The constant source drawn at the bottom of the circuit. -/
structure VoltageSource where
  potentialRise : ElectricPotentialQuantity
  isConstant : Bool

/-- Component identities used to transcribe the single-loop drawing. -/
inductive CircuitComponent where
  | diode
  | resistorR
  | voltageSource
  deriving DecidableEq, Repr

/-!
Figure-derived topology and annotations.  The three positions describe one
cyclic traversal of the loop, beginning with the diode at the upper left.
-/
structure SeriesCircuitFigure where
  componentAt : Fin 3 → CircuitComponent
  sourcePrintedVoltageInVolts : ℝ
  resistorPrintedLabel : String
  formsSingleClosedLoop : Bool
  diodeSymbolShowsForwardOrientation : Bool

/-- The physical objects and unknown quantities in the depicted circuit. -/
structure SeriesDiodeCircuit where
  diode : Diode
  resistor : Resistor
  source : VoltageSource
  connectedDiodeBias : DiodeBias
  seriesCurrent : ElectricCurrentQuantity
  figure : SeriesCircuitFigure

/-! ## Scenario and primary-figure readouts -/

/-!
The prose supplies the preliminary reverse-current measurement and says that
the same diode is subsequently connected in forward bias to a constant source.
These hypotheses do not specify the resistor voltage.
-/
structure MatchesStatedDiodeScenario (setup : SeriesDiodeCircuit) : Prop where
  reverseCurrentReadout :
    currentInAmperes setup.diode.reverseBiasCurrent = (1 : ℝ) / 10 ^ 5
  connectedInForwardBias : setup.connectedDiodeBias = .forward
  sourceIsConstant : setup.source.isConstant = true

/-!
Direct transcription of the supplied bitmap: one closed series loop, diode,
resistor `R`, and a source labelled `6 volts`.
-/
structure MatchesSuppliedSeriesCircuitFigure
    (setup : SeriesDiodeCircuit) : Prop where
  firstComponent : setup.figure.componentAt 0 = .diode
  secondComponent : setup.figure.componentAt 1 = .resistorR
  thirdComponent : setup.figure.componentAt 2 = .voltageSource
  oneClosedLoop : setup.figure.formsSingleClosedLoop = true
  forwardOrientation : setup.figure.diodeSymbolShowsForwardOrientation = true
  resistorLabel : setup.figure.resistorPrintedLabel = "R"
  componentResistorLabelAgrees :
    setup.resistor.printedLabel = setup.figure.resistorPrintedLabel
  printedSourceVoltage : setup.figure.sourcePrintedVoltageInVolts = 6
  sourceMatchesPrintedVoltage :
    potentialInVolts setup.source.potentialRise =
      setup.figure.sourcePrintedVoltageInVolts

/-! ## Governing physical models -/

/-!
A textbook diode-identification model: a reverse leakage current at least one
microampere places the diode in the germanium class, whose nominal forward drop
is `0.3 V`.  This encodes the physical inference for which the supplied reverse
current is relevant; it does not mention the requested resistor drop.
-/
structure SatisfiesTextbookDiodeModel
    (setup : SeriesDiodeCircuit) : Prop where
  leakageScaleIdentifiesGermanium :
    (1 : ℝ) / 10 ^ 6 ≤ currentInAmperes setup.diode.reverseBiasCurrent →
      setup.diode.material = .germanium
  germaniumNominalForwardDrop :
    setup.connectedDiodeBias = .forward →
      setup.diode.material = .germanium →
        potentialInVolts setup.diode.forwardVoltageDrop = (3 : ℝ) / 10

/-!
Kirchhoff's voltage law for the one source, diode, and resistor in the loop,
together with Ohm's law for `R`.  Both are stated for the independent physical
fields of `setup`, rather than by defining any field from the desired answer.
-/
structure SatisfiesSeriesCircuitLaws (setup : SeriesDiodeCircuit) : Prop where
  kirchhoffVoltageLaw :
    potentialInVolts setup.source.potentialRise =
      potentialInVolts setup.diode.forwardVoltageDrop +
        potentialInVolts setup.resistor.voltageDrop
  resistorOhmLaw :
    potentialInVolts setup.resistor.voltageDrop =
      currentInAmperes setup.seriesCurrent *
        resistanceInOhms setup.resistor.resistance
  positiveResistance : 0 < resistanceInOhms setup.resistor.resistance

/-! ## Printed answer choices and target -/

/-- Labels of the four voltage-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical voltage printed beside each answer-choice label. -/
def answerChoiceVoltageInVolts : AnswerChoice → ℝ
  | .A => 67 / 10
  | .B => 157 / 10
  | .C => 57 / 10
  | .D => 47 / 10

/-!
Blueprint label: `thm:physics:phyx_mini_0572:target`.

Under the stated measurement, the primary figure, the textbook diode model,
and the ordinary series-circuit laws, the resistor drop matches choice C,
namely `5.7 V`.
-/
theorem resistor_voltage_drop_matches_choice_C
    (setup : SeriesDiodeCircuit)
    (scenario : MatchesStatedDiodeScenario setup)
    (figure : MatchesSuppliedSeriesCircuitFigure setup)
    (diodeModel : SatisfiesTextbookDiodeModel setup)
    (circuitLaws : SatisfiesSeriesCircuitLaws setup) :
    potentialInVolts setup.resistor.voltageDrop =
      answerChoiceVoltageInVolts .C := by
  have leakageThreshold : (1 : ℝ) / 10 ^ 6 ≤
      currentInAmperes setup.diode.reverseBiasCurrent := by
    rw [scenario.reverseCurrentReadout]
    norm_num
  have germanium : setup.diode.material = .germanium :=
    diodeModel.leakageScaleIdentifiesGermanium leakageThreshold
  have diodeDrop :
      potentialInVolts setup.diode.forwardVoltageDrop = (3 : ℝ) / 10 :=
    diodeModel.germaniumNominalForwardDrop
      scenario.connectedInForwardBias germanium
  have sourcePotential :
      potentialInVolts setup.source.potentialRise = 6 := by
    calc
      potentialInVolts setup.source.potentialRise =
          setup.figure.sourcePrintedVoltageInVolts :=
        figure.sourceMatchesPrintedVoltage
      _ = 6 := figure.printedSourceVoltage
  change potentialInVolts setup.resistor.voltageDrop = (57 : ℝ) / 10
  linarith [circuitLaws.kirchhoffVoltageLaw, diodeDrop, sourcePotential]

end PhyXMiniProblems.ProblemPhyXMini0572
