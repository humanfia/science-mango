import Mathlib.Analysis.SpecialFunctions.Exp
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0629

open Dimension

/-!
# Half-wave rectifier with a Shockley diode

The primary image shows an AC source labelled `V_in`, a resistor labelled `R`,
and a diode in one series loop.  The current arrow `I` points downward through
the diode, and the output terminals labelled `V_out` are connected across the
diode with their positive terminal at the top.

The prose supplies the diode saturation current `5 * 10^-13 A` and temperature
`300 K`.  Neither the prose nor the image supplies an input-voltage operating
point or a resistance value.  Both therefore remain explicit physical
parameters; no missing numerical datum is invented below.

Assumption/target split:

* governing laws: branch-current continuity, Kirchhoff's voltage law, Ohm's
  law for `R`, and the ideal Shockley diode equation;
* previous-part results: none;
* figure/data readouts: all four printed labels, the source/output polarities,
  the series topology, the downward forward-current orientation,
  `I_S = 5 * 10^-13 A`, and `T = 300 K`;
* current target conclusion: the indicated current satisfies the implicit
  current equation obtained by eliminating the resistor and diode voltage
  drops from Kirchhoff's, Ohm's, and Shockley's laws.

The printed choice A (`0.006 A`) is retained below as dataset metadata, but it
is not asserted as a physical consequence: the source gives neither the
instantaneous value of `V_in` nor the value of `R` needed to determine it.

Electrical quantities are unit-independent Physlib `Dimensionful` objects.
Real numbers are used only for coherent-SI readouts and dimensionless factors.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has physical dimension potential per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- A signed, unit-independent electric current.  Its sign is relative to a
chosen branch orientation. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent electric potential difference. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Read an electric current in coherent SI units, hence in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  (current UnitChoices.SI).val

/-- Read a potential difference in coherent SI units, hence in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read a resistance in coherent SI units, hence in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- The numerical size, in coulombs, of one elementary positive charge.
Physlib represents this calibrated constant as a charge-unit scale. -/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Physical components and operating-point quantities -/

/-- The resistor marked `R` in the primary figure. -/
structure Resistor where
  printedLabel : String
  resistance : ElectricalResistanceQuantity
  voltageDrop : ElectricPotentialQuantity
  current : ElectricCurrentQuantity

/-- The forward-oriented diode in the primary figure. -/
structure Diode where
  saturationCurrent : ElectricCurrentQuantity
  voltageDrop : ElectricPotentialQuantity
  current : ElectricCurrentQuantity
  /-- Dimensionless emission/ideality factor in the Shockley model. -/
  idealityFactor : ℝ

/-- Vertical directions used to transcribe the current arrow and diode
orientation in the image. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Labels, polarity marks, and topology read directly from the primary image. -/
structure HalfWaveRectifierFigure where
  inputVoltageLabel : String
  resistorLabel : String
  currentLabel : String
  outputVoltageLabel : String
  sourceTopTerminalPositive : Bool
  outputTopTerminalPositive : Bool
  currentArrowDirection : VerticalDirection
  forwardCurrentDirection : VerticalDirection
  resistorAndDiodeFormSeriesLoop : Bool
  outputTerminalsAreAcrossDiode : Bool

/-- A single instantaneous operating point of the depicted half-wave
rectifier.  In particular, `inputVoltage` is the instantaneous AC-source
voltage, not an amplitude or RMS value. -/
structure HalfWaveRectifierOperatingPoint where
  inputVoltage : ElectricPotentialQuantity
  outputVoltage : ElectricPotentialQuantity
  indicatedCurrent : ElectricCurrentQuantity
  resistor : Resistor
  diode : Diode
  temperature : Temperature
  temperatureUnit : TemperatureUnit
  figure : HalfWaveRectifierFigure

/-! ## Scenario data and primary-figure readouts -/

/-- The two numerical data supplied by the prose.  The temperature value is
paired with an explicit kelvin-unit assertion because `Temperature` itself is
stored in an arbitrary absolute-temperature scale. -/
structure MatchesStatedRectifierData
    (setup : HalfWaveRectifierOperatingPoint) : Prop where
  saturationCurrentInAmperes :
    currentInAmperes setup.diode.saturationCurrent = (5 : ℝ) / 10 ^ 13
  saturationCurrentPositive :
    0 < currentInAmperes setup.diode.saturationCurrent
  temperatureUnitIsKelvin :
    setup.temperatureUnit = TemperatureUnit.kelvin
  temperatureIs300 :
    setup.temperature = Temperature.ofNNReal 300

/-- Direct transcription of the component labels, polarity marks, topology,
and downward current orientation in the supplied bitmap. -/
structure MatchesSuppliedHalfWaveRectifierFigure
    (setup : HalfWaveRectifierOperatingPoint) : Prop where
  inputLabel : setup.figure.inputVoltageLabel = "V_in"
  resistorLabel : setup.figure.resistorLabel = "R"
  currentLabel : setup.figure.currentLabel = "I"
  outputLabel : setup.figure.outputVoltageLabel = "V_out"
  sourcePolarity : setup.figure.sourceTopTerminalPositive = true
  outputPolarity : setup.figure.outputTopTerminalPositive = true
  arrowPointsDownward :
    setup.figure.currentArrowDirection = .downward
  forwardCurrentPointsDownward :
    setup.figure.forwardCurrentDirection = .downward
  seriesLoop : setup.figure.resistorAndDiodeFormSeriesLoop = true
  outputAcrossDiode : setup.figure.outputTerminalsAreAcrossDiode = true
  componentResistorLabelAgrees :
    setup.resistor.printedLabel = setup.figure.resistorLabel
  outputEqualsDiodeDrop : setup.outputVoltage = setup.diode.voltageDrop

/-! ## Governing physical laws -/

/-- The operating point lies on the source's forward half-cycle relative to
the polarities and current direction drawn in the figure.  These sign facts do
not prescribe the magnitude of the requested current. -/
structure IsForwardBiasedOperatingPoint
    (setup : HalfWaveRectifierOperatingPoint) : Prop where
  inputVoltagePositive : 0 < potentialInVolts setup.inputVoltage
  diodeVoltageNonnegative : 0 ≤ potentialInVolts setup.diode.voltageDrop
  downwardCurrentNonnegative : 0 ≤ currentInAmperes setup.indicatedCurrent

/-- Kirchhoff/Ohm laws for the one-loop circuit and the ideal Shockley law for
the diode.  The exponential argument is the dimensionless SI ratio
`q V_D / (n k_B T)`.  No field or hypothesis mentions the requested
`0.006 A` conclusion. -/
structure SatisfiesHalfWaveRectifierLaws
    (setup : HalfWaveRectifierOperatingPoint) : Prop where
  resistorCarriesIndicatedCurrent :
    setup.resistor.current = setup.indicatedCurrent
  diodeCarriesIndicatedCurrent :
    setup.diode.current = setup.indicatedCurrent
  kirchhoffVoltageLaw :
    potentialInVolts setup.inputVoltage =
      potentialInVolts setup.resistor.voltageDrop +
        potentialInVolts setup.diode.voltageDrop
  resistorOhmLaw :
    potentialInVolts setup.resistor.voltageDrop =
      currentInAmperes setup.resistor.current *
        resistanceInOhms setup.resistor.resistance
  resistancePositive : 0 < resistanceInOhms setup.resistor.resistance
  idealDiodeFactor : setup.diode.idealityFactor = 1
  shockleyDiodeLaw :
    currentInAmperes setup.diode.current =
      currentInAmperes setup.diode.saturationCurrent *
        (Real.exp
          (elementaryChargeInCoulombs *
              potentialInVolts setup.diode.voltageDrop /
            (setup.diode.idealityFactor * Constants.kB *
              (setup.temperature : ℝ))) - 1)

/-! ## Printed answer choices and target -/

/-- Labels of the four current-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical current in amperes printed beside each answer-choice label. -/
def answerChoiceCurrentInAmperes : AnswerChoice → ℝ
  | .A => 6 / 1000
  | .B => 7 / 1000
  | .C => 60 / 1000
  | .D => 5 / 1000

/-!
Blueprint label: `thm:physics:phyx_mini_0629:target`.

For an operating point matching the stated data, supplied image, forward-bias
orientation, and ordinary resistor/diode laws, the downward indicated current
satisfies the implicit loop equation obtained as follows: substitute Ohm's law
for the resistor drop into Kirchhoff's voltage law, then substitute the
resulting diode drop into the Shockley equation.

The declaration name is retained for compatibility with the blueprint pin.
Choice A remains source metadata only: because the source omits numerical
values for the instantaneous input voltage and resistance, no particular
numerical current follows from these premises.
-/
theorem rectifier_current_matches_choice_A
    (setup : HalfWaveRectifierOperatingPoint)
    (data : MatchesStatedRectifierData setup)
    (figure : MatchesSuppliedHalfWaveRectifierFigure setup)
    (forwardBias : IsForwardBiasedOperatingPoint setup)
    (laws : SatisfiesHalfWaveRectifierLaws setup) :
    currentInAmperes setup.indicatedCurrent =
      currentInAmperes setup.diode.saturationCurrent *
        (Real.exp
          (elementaryChargeInCoulombs *
              (potentialInVolts setup.inputVoltage -
                currentInAmperes setup.indicatedCurrent *
                  resistanceInOhms setup.resistor.resistance) /
            (setup.diode.idealityFactor * Constants.kB *
              (setup.temperature : ℝ))) - 1) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0629
