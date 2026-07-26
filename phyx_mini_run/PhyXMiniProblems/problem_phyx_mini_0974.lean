import Mathlib
import Physlib.Electromagnetism.Dynamics.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0974

open Dimension

/-!
# Current induced in a nearby rectangular coil by an RC discharge

The large circuit contains a charged capacitor, a resistor, and a switch.  A
separate stationary `25`-turn rectangular circuit lies to the right of the
large circuit.  Under the stated approximation, only the nearest vertical
wire of the large circuit contributes appreciably to the magnetic flux
through the small circuit.

Physical capacitances, voltages, resistances, lengths, times, currents,
magnetic-flux densities, fluxes, and emfs are represented by Physlib's
unit-independent `Dimensionful` quantities.  Real numbers are used only for
coherent-SI readouts, scalar time profiles, and displayed answer values.

Assumption/target split:

* governing laws: exponential RC discharge, the long-straight-wire field,
  integration of that field across the rectangular coil, Faraday's law,
  wire resistance from resistance per unit length, and Ohm's law;
* previous-part results: none;
* figure/data readouts: the shown polarity and open switch, labels `C`, `R0`,
  `S`, `a`, `b`, and `c`, all numerical component and geometry data, electrical
  isolation, stationarity, `25` turns, and the nearest-wire approximation;
* current target conclusions: the induced-current closed form at `200 μs`,
  its exact value `log 3 / (300 e) A` under the literal data, and the fact that
  this value agrees with none of the four displayed choices.

No target current or answer choice is a setup or premise field.

The source literally states `1.0 Ω/m`.  With `25` turns of a `0.10 m` by
`0.20 m` rectangle this gives `15 Ω` and a current of about `0.001347 A`.
The recorded `1.33 A` choice instead requires a resistance per length smaller
by a factor of about `1000`.  The formalization preserves B as dataset
metadata, but its theorem states the result supported by the literal data.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of voltage and electromotive force. -/
def voltageDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def resistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M⁻¹ L⁻² T² C²` of capacitance. -/
def capacitanceDimension : Dimension :=
  M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * C𝓭 * C𝓭

/-- The dimension `M L T⁻¹ C⁻²` of resistance per unit length. -/
def resistancePerLengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻¹` of magnetic flux. -/
def magneticFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent physical time coordinate. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent capacitance. -/
abbrev CapacitanceMagnitude : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A signed, unit-independent voltage. -/
abbrev SignedVoltage : Type :=
  Dimensionful (WithDim voltageDimension ℝ)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim resistanceDimension NNReal)

/-- A nonnegative resistance per unit length. -/
abbrev ResistancePerLengthMagnitude : Type :=
  Dimensionful (WithDim resistancePerLengthDimension NNReal)

/-- A signed, unit-independent electric current. -/
abbrev SignedElectricCurrent : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed normal component of magnetic flux density. -/
abbrev SignedMagneticFluxDensity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension ℝ)

/-- Signed magnetic flux through one oriented turn. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Read a physical time coordinate in coherent-SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a physical time coordinate in microseconds. -/
def timeInMicroseconds (time : TimeQuantity) : ℝ :=
  1_000_000 * timeInSeconds time

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical capacitance in coherent-SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceMagnitude) : ℝ :=
  ((capacitance UnitChoices.SI).val : ℝ)

/-- Read a physical capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceMagnitude) : ℝ :=
  1_000_000 * capacitanceInFarads capacitance

/-- Read a signed voltage or emf in coherent-SI volts. -/
def voltageInVolts (voltage : SignedVoltage) : ℝ :=
  (voltage UnitChoices.SI).val

/-- Read a physical resistance in coherent-SI ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Read resistance per length in coherent-SI ohms per metre. -/
def resistancePerLengthInOhmsPerMeter
    (resistancePerLength : ResistancePerLengthMagnitude) : ℝ :=
  ((resistancePerLength UnitChoices.SI).val : ℝ)

/-- Read a signed electric current in coherent-SI amperes. -/
def currentInAmperes (current : SignedElectricCurrent) : ℝ :=
  (current UnitChoices.SI).val

/-- Read a signed magnetic-flux-density component in teslas. -/
def magneticFluxDensityInTeslas
    (field : SignedMagneticFluxDensity) : ℝ :=
  (field UnitChoices.SI).val

/-- Read signed magnetic flux in coherent-SI webers. -/
def magneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## Circuit and primary-figure vocabulary -/

/-- Text labels visible in the supplied circuit diagram. -/
inductive FigureLabel where
  | capacitorC
  | resistorR0
  | switchS
  | smallWidthA
  | smallHeightB
  | separationC
  deriving DecidableEq, Fintype, Repr

/-- The two capacitor plates as drawn on the page. -/
inductive CapacitorPlate where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- How the switch is drawn, independently of its later dynamical state. -/
inductive SwitchDepiction where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Geometric roles of the three labels on and between the loops. -/
inductive DimensionLabelRole where
  | smallHorizontalWidth
  | smallVerticalHeight
  | horizontalInterCircuitGap
  deriving DecidableEq, Repr

/-- Which conductor is retained in the stated magnetic-field approximation. -/
inductive FieldSourceApproximation where
  | nearestLargeVerticalWireOnly
  | allLargeCircuitSegments
  deriving DecidableEq, Repr

/-!
Literal, qualitative information visible in image `974.png`.  Numerical
lengths are problem-text data and are therefore kept out of this record.
-/
structure CoupledCircuitFigure where
  labelIsShown : FigureLabel → Bool
  positiveCapacitorPlate : CapacitorPlate
  switchDepiction : SwitchDepiction
  largeLoopIsLeftOfSmallLoop : Bool
  smallLoopIsRectangular : Bool
  nearestLargeWireIsVertical : Bool
  dimensionLabelRole : FigureLabel → Option DimensionLabelRole

/-! ## Independent apparatus quantities and observables -/

/-!
Independent physical data for the two circuits.  The time-dependent current,
field, flux, and emf observables are not defined from circuit parameters or
from an answer choice; the governing-law predicates below relate them.
-/
structure RCInductionSetup where
  freeSpace : Electromagnetism.FreeSpace
  capacitance : CapacitanceMagnitude
  initialCapacitorVoltage : SignedVoltage
  largeCircuitResistance : ResistanceMagnitude
  largeLoopHorizontalWidth : LengthMagnitude
  largeLoopVerticalHeight : LengthMagnitude
  smallLoopHorizontalWidth : LengthMagnitude
  smallLoopVerticalHeight : LengthMagnitude
  interCircuitSeparation : LengthMagnitude
  smallWireResistancePerLength : ResistancePerLengthMagnitude
  totalSmallWireLength : LengthMagnitude
  smallCircuitResistance : ResistanceMagnitude
  turnCount : ℕ
  switchClosureTime : TimeQuantity
  observationTime : TimeQuantity
  timeAtSeconds : ℝ → TimeQuantity
  largeCircuitCurrent : TimeQuantity → SignedElectricCurrent
  nearestWireFieldAtDistance :
    TimeQuantity → LengthMagnitude → SignedMagneticFluxDensity
  magneticFluxPerTurn : TimeQuantity → SignedMagneticFlux
  inducedEmf : TimeQuantity → SignedVoltage
  smallCircuitCurrent : TimeQuantity → SignedElectricCurrent
  circuitsElectricallyConnected : Bool
  bothCircuitsHeldStationary : Bool
  fieldSourceApproximation : FieldSourceApproximation
  figure : CoupledCircuitFigure

/-! ## Scalar profiles obtained from independent physical observables -/

/-- Large-circuit current profile, with the argument measured in seconds. -/
def largeCurrentInAmperesAtSeconds
    (setup : RCInductionSetup) (seconds : ℝ) : ℝ :=
  currentInAmperes (setup.largeCircuitCurrent (setup.timeAtSeconds seconds))

/-- Nearest-wire field component at a physical distance and scalar time. -/
def nearestWireFieldInTeslasAtSeconds
    (setup : RCInductionSetup) (seconds : ℝ) (distance : LengthMagnitude) : ℝ :=
  magneticFluxDensityInTeslas
    (setup.nearestWireFieldAtDistance (setup.timeAtSeconds seconds) distance)

/-- Per-turn magnetic-flux profile, with the argument measured in seconds. -/
def fluxPerTurnInWebersAtSeconds
    (setup : RCInductionSetup) (seconds : ℝ) : ℝ :=
  magneticFluxInWebers (setup.magneticFluxPerTurn (setup.timeAtSeconds seconds))

/-- Induced-emf profile, with the argument measured in seconds. -/
def inducedEmfInVoltsAtSeconds
    (setup : RCInductionSetup) (seconds : ℝ) : ℝ :=
  voltageInVolts (setup.inducedEmf (setup.timeAtSeconds seconds))

/-- Small-circuit current profile, with the argument measured in seconds. -/
def smallCurrentInAmperesAtSeconds
    (setup : RCInductionSetup) (seconds : ℝ) : ℝ :=
  currentInAmperes (setup.smallCircuitCurrent (setup.timeAtSeconds seconds))

/-! ## Figure evidence and problem-statement data -/

/-- Literal labels, polarity, and geometry transcribed from the primary image. -/
structure MatchesPrimaryCircuitFigure (setup : RCInductionSetup) : Prop where
  everyNamedLabelIsShown : ∀ label, setup.figure.labelIsShown label = true
  upperCapacitorPlateIsPositive :
    setup.figure.positiveCapacitorPlate = .upper
  switchIsDrawnOpen : setup.figure.switchDepiction = .open
  largeLoopIsOnLeft : setup.figure.largeLoopIsLeftOfSmallLoop = true
  smallLoopIsRectangle : setup.figure.smallLoopIsRectangular = true
  nearestLargeWireIsVertical : setup.figure.nearestLargeWireIsVertical = true
  aLabelsHorizontalWidth :
    setup.figure.dimensionLabelRole .smallWidthA =
      some .smallHorizontalWidth
  bLabelsVerticalHeight :
    setup.figure.dimensionLabelRole .smallHeightB =
      some .smallVerticalHeight
  cLabelsHorizontalGap :
    setup.figure.dimensionLabelRole .separationC =
      some .horizontalInterCircuitGap

/-!
All numerical and qualitative data stated in the problem text.  In particular,
the resistance-per-length field preserves the literal `1.0 Ω/m` wording.
-/
structure MatchesProblemDescription (setup : RCInductionSetup) : Prop where
  capacitanceIsTwentyMicrofarads :
    capacitanceInMicrofarads setup.capacitance = 20
  initialVoltageIsOneHundredVolts :
    voltageInVolts setup.initialCapacitorVoltage = 100
  largeResistanceIsTenOhms :
    resistanceInOhms setup.largeCircuitResistance = 10
  largeLoopWidthIsTwoMeters :
    lengthInMeters setup.largeLoopHorizontalWidth = 2
  largeLoopHeightIsFourMeters :
    lengthInMeters setup.largeLoopVerticalHeight = 4
  smallWidthAIsTenCentimeters :
    lengthInCentimeters setup.smallLoopHorizontalWidth = 10
  smallHeightBIsTwentyCentimeters :
    lengthInCentimeters setup.smallLoopVerticalHeight = 20
  separationCIsFiveCentimeters :
    lengthInCentimeters setup.interCircuitSeparation = 5
  wireResistanceIsOneOhmPerMeter :
    resistancePerLengthInOhmsPerMeter
      setup.smallWireResistancePerLength = 1
  smallCircuitHasTwentyFiveTurns : setup.turnCount = 25
  switchClosesAtZero : timeInSeconds setup.switchClosureTime = 0
  asksForCurrentAtTwoHundredMicroseconds :
    timeInMicroseconds setup.observationTime = 200
  circuitsAreElectricallyIsolated :
    setup.circuitsElectricallyConnected = false
  circuitsAreStationary : setup.bothCircuitsHeldStationary = true
  onlyNearestWireIsAppreciable :
    setup.fieldSourceApproximation = .nearestLargeVerticalWireOnly

/-- Positivity and nondegeneracy of the physical branch of the model. -/
structure HasPhysicalCircuitParameters (setup : RCInductionSetup) : Prop where
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  initialVoltagePositive : 0 < voltageInVolts setup.initialCapacitorVoltage
  largeResistancePositive :
    0 < resistanceInOhms setup.largeCircuitResistance
  largeLoopWidthPositive :
    0 < lengthInMeters setup.largeLoopHorizontalWidth
  largeLoopHeightPositive :
    0 < lengthInMeters setup.largeLoopVerticalHeight
  smallWidthPositive : 0 < lengthInMeters setup.smallLoopHorizontalWidth
  smallHeightPositive : 0 < lengthInMeters setup.smallLoopVerticalHeight
  separationPositive : 0 < lengthInMeters setup.interCircuitSeparation
  wireResistancePerLengthPositive :
    0 < resistancePerLengthInOhmsPerMeter
      setup.smallWireResistancePerLength
  totalSmallWireLengthPositive :
    0 < lengthInMeters setup.totalSmallWireLength
  smallResistancePositive :
    0 < resistanceInOhms setup.smallCircuitResistance
  turnCountPositive : 0 < setup.turnCount
  observationAfterClosure :
    timeInSeconds setup.switchClosureTime <
      timeInSeconds setup.observationTime

/-! ## Governing physical laws -/

/-- The scalar time parameter really is the coherent-SI second coordinate. -/
structure HasCoherentSecondCoordinate (setup : RCInductionSetup) : Prop where
  timeCoordinateCalibration : ∀ seconds : ℝ,
    timeInSeconds (setup.timeAtSeconds seconds) = seconds

/-!
The textbook value of vacuum permeability in coherent SI units.  Physlib's
`Electromagnetism.FreeSpace` supplies positivity of this independent constant.
-/
structure UsesTextbookVacuumPermeability (setup : RCInductionSetup) : Prop where
  vacuumPermeabilityValue :
    setup.freeSpace.μ₀ = 4 * Real.pi / 10_000_000

/-! Exponential discharge current after the switch closes. -/
structure SatisfiesRCDischargeLaw (setup : RCInductionSetup) : Prop where
  dischargeCurrentLaw : ∀ seconds : ℝ,
    timeInSeconds setup.switchClosureTime ≤ seconds →
      largeCurrentInAmperesAtSeconds setup seconds =
        voltageInVolts setup.initialCapacitorVoltage /
          resistanceInOhms setup.largeCircuitResistance *
            Real.exp
              (-(seconds - timeInSeconds setup.switchClosureTime) /
                (resistanceInOhms setup.largeCircuitResistance *
                  capacitanceInFarads setup.capacitance))

/-!
The signed normal field component on the small-loop side of the retained
straight vertical wire.  The radial domain is exactly the strip occupied by
the small rectangle.
-/
structure SatisfiesNearestStraightWireFieldLaw
    (setup : RCInductionSetup) : Prop where
  straightWireFieldLaw : ∀ (seconds : ℝ) (distance : LengthMagnitude),
    timeInSeconds setup.switchClosureTime ≤ seconds →
    lengthInMeters setup.interCircuitSeparation ≤ lengthInMeters distance →
    lengthInMeters distance ≤
        lengthInMeters setup.interCircuitSeparation +
          lengthInMeters setup.smallLoopHorizontalWidth →
      nearestWireFieldInTeslasAtSeconds setup seconds distance =
        setup.freeSpace.μ₀ * largeCurrentInAmperesAtSeconds setup seconds /
          (2 * Real.pi * lengthInMeters distance)

/-!
The result of integrating the retained `1/r` field across the horizontal
width `a` and multiplying by the vertical height `b`.  This is a general
one-turn flux law and contains no answer-current value.
-/
structure SatisfiesRectangularStraightWireFluxLaw
    (setup : RCInductionSetup) : Prop where
  rectangularFluxLaw : ∀ seconds : ℝ,
    timeInSeconds setup.switchClosureTime ≤ seconds →
      fluxPerTurnInWebersAtSeconds setup seconds =
        setup.freeSpace.μ₀ *
          lengthInMeters setup.smallLoopVerticalHeight *
          largeCurrentInAmperesAtSeconds setup seconds /
          (2 * Real.pi) *
          Real.log
            ((lengthInMeters setup.interCircuitSeparation +
                lengthInMeters setup.smallLoopHorizontalWidth) /
              lengthInMeters setup.interCircuitSeparation)

/-- Faraday's law for `N` turns, including the Lenz-law sign. -/
structure SatisfiesFaradayLaw (setup : RCInductionSetup) : Prop where
  faradayLaw : ∀ seconds : ℝ,
    timeInSeconds setup.switchClosureTime < seconds →
      inducedEmfInVoltsAtSeconds setup seconds =
        -(setup.turnCount : ℝ) *
          deriv (fluxPerTurnInWebersAtSeconds setup) seconds

/-! The coil wire length and resistance follow from its rectangular winding. -/
structure SatisfiesSmallWireResistanceLaw
    (setup : RCInductionSetup) : Prop where
  windingLengthLaw :
    lengthInMeters setup.totalSmallWireLength =
      (setup.turnCount : ℝ) *
        2 * (lengthInMeters setup.smallLoopHorizontalWidth +
          lengthInMeters setup.smallLoopVerticalHeight)
  resistanceFromWireLength :
    resistanceInOhms setup.smallCircuitResistance =
      resistancePerLengthInOhmsPerMeter
          setup.smallWireResistancePerLength *
        lengthInMeters setup.totalSmallWireLength

/-- Ohm's law for the electrically isolated small circuit. -/
structure SatisfiesSmallCircuitOhmsLaw
    (setup : RCInductionSetup) : Prop where
  smallCircuitOhmsLaw : ∀ seconds : ℝ,
    timeInSeconds setup.switchClosureTime < seconds →
      smallCurrentInAmperesAtSeconds setup seconds =
        inducedEmfInVoltsAtSeconds setup seconds /
          resistanceInOhms setup.smallCircuitResistance

/-! ## Derived closed form and displayed answer semantics -/

/-!
The current obtained by differentiating the RC/straight-wire flux expression
and applying Faraday plus Ohm.  This definition depends only on independent
apparatus parameters and time; it contains no displayed answer value.
-/
def rcStraightWireClosedFormInAmperes
    (setup : RCInductionSetup) (seconds : ℝ) : ℝ :=
  (setup.turnCount : ℝ) * setup.freeSpace.μ₀ *
      lengthInMeters setup.smallLoopVerticalHeight *
      voltageInVolts setup.initialCapacitorVoltage *
      Real.log
        ((lengthInMeters setup.interCircuitSeparation +
            lengthInMeters setup.smallLoopHorizontalWidth) /
          lengthInMeters setup.interCircuitSeparation) *
      Real.exp
        (-(seconds - timeInSeconds setup.switchClosureTime) /
          (resistanceInOhms setup.largeCircuitResistance *
            capacitanceInFarads setup.capacitance)) /
    (2 * Real.pi * resistanceInOhms setup.smallCircuitResistance *
      resistanceInOhms setup.largeCircuitResistance ^ 2 *
      capacitanceInFarads setup.capacitance)

/-- Magnitude of the requested observable at the stated observation time. -/
def observedSmallCurrentMagnitudeInAmperes
    (setup : RCInductionSetup) : ℝ :=
  |smallCurrentInAmperesAtSeconds setup
    (timeInSeconds setup.observationTime)|

/-- Labels of the four displayed current choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current magnitude printed beside each answer label, in amperes. -/
def AnswerChoice.currentMagnitudeInAmperes : AnswerChoice → ℝ
  | .A => 89 / 100
  | .B => 133 / 100
  | .C => 1
  | .D => 5 / 2

/-- Dataset metadata recording answer B; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The governing laws give the independent small-circuit current observable the
standard RC/straight-wire closed form.  This helper has no answer-choice
conclusion.
-/
lemma observedSmallCurrent_eq_closedForm
    (setup : RCInductionSetup)
    (_physical : HasPhysicalCircuitParameters setup)
    (_timeCoordinate : HasCoherentSecondCoordinate setup)
    (_rc : SatisfiesRCDischargeLaw setup)
    (_field : SatisfiesNearestStraightWireFieldLaw setup)
    (_flux : SatisfiesRectangularStraightWireFluxLaw setup)
    (_faraday : SatisfiesFaradayLaw setup)
    (_wireResistance : SatisfiesSmallWireResistanceLaw setup)
    (_ohm : SatisfiesSmallCircuitOhmsLaw setup) :
    observedSmallCurrentMagnitudeInAmperes setup =
      |rcStraightWireClosedFormInAmperes setup
        (timeInSeconds setup.observationTime)| := by
  have hObservation :
      timeInSeconds setup.switchClosureTime <
        timeInSeconds setup.observationTime :=
    _physical.observationAfterClosure
  have hFluxNearObservation :
      fluxPerTurnInWebersAtSeconds setup =ᶠ[
          nhds (timeInSeconds setup.observationTime)]
        fun seconds =>
          setup.freeSpace.μ₀ *
            lengthInMeters setup.smallLoopVerticalHeight *
            (voltageInVolts setup.initialCapacitorVoltage /
              resistanceInOhms setup.largeCircuitResistance *
              Real.exp
                (-(seconds - timeInSeconds setup.switchClosureTime) /
                  (resistanceInOhms setup.largeCircuitResistance *
                    capacitanceInFarads setup.capacitance))) /
            (2 * Real.pi) *
            Real.log
              ((lengthInMeters setup.interCircuitSeparation +
                  lengthInMeters setup.smallLoopHorizontalWidth) /
                lengthInMeters setup.interCircuitSeparation) := by
    filter_upwards [Ioi_mem_nhds hObservation] with seconds hSeconds
    rw [_flux.rectangularFluxLaw seconds hSeconds.le,
      _rc.dischargeCurrentLaw seconds hSeconds.le]
  have hExpDerivative :
      HasDerivAt
        (fun seconds : ℝ =>
          Real.exp
            (-(seconds - timeInSeconds setup.switchClosureTime) /
              (resistanceInOhms setup.largeCircuitResistance *
                capacitanceInFarads setup.capacitance)))
        (Real.exp
            (-(timeInSeconds setup.observationTime -
                timeInSeconds setup.switchClosureTime) /
              (resistanceInOhms setup.largeCircuitResistance *
                capacitanceInFarads setup.capacitance)) *
          (-(1 : ℝ) /
            (resistanceInOhms setup.largeCircuitResistance *
              capacitanceInFarads setup.capacitance)))
        (timeInSeconds setup.observationTime) := by
    convert
      (((hasDerivAt_id (𝕜 := ℝ)
          (timeInSeconds setup.observationTime)).sub_const
            (timeInSeconds setup.switchClosureTime)).neg.div_const
              (resistanceInOhms setup.largeCircuitResistance *
                capacitanceInFarads setup.capacitance)).exp using 1
    · ext seconds
      congr 1
    · congr 1
  have hFluxModelDerivative :
      HasDerivAt
        (fun seconds =>
          setup.freeSpace.μ₀ *
            lengthInMeters setup.smallLoopVerticalHeight *
            (voltageInVolts setup.initialCapacitorVoltage /
              resistanceInOhms setup.largeCircuitResistance *
              Real.exp
                (-(seconds - timeInSeconds setup.switchClosureTime) /
                  (resistanceInOhms setup.largeCircuitResistance *
                    capacitanceInFarads setup.capacitance))) /
            (2 * Real.pi) *
            Real.log
              ((lengthInMeters setup.interCircuitSeparation +
                  lengthInMeters setup.smallLoopHorizontalWidth) /
                lengthInMeters setup.interCircuitSeparation))
        (setup.freeSpace.μ₀ *
            lengthInMeters setup.smallLoopVerticalHeight *
            (voltageInVolts setup.initialCapacitorVoltage /
              resistanceInOhms setup.largeCircuitResistance *
              (Real.exp
                  (-(timeInSeconds setup.observationTime -
                      timeInSeconds setup.switchClosureTime) /
                    (resistanceInOhms setup.largeCircuitResistance *
                      capacitanceInFarads setup.capacitance)) *
                (-(1 : ℝ) /
                  (resistanceInOhms setup.largeCircuitResistance *
                    capacitanceInFarads setup.capacitance)))) /
            (2 * Real.pi) *
            Real.log
              ((lengthInMeters setup.interCircuitSeparation +
                  lengthInMeters setup.smallLoopHorizontalWidth) /
                lengthInMeters setup.interCircuitSeparation))
        (timeInSeconds setup.observationTime) := by
    exact
      ((((hExpDerivative.const_mul
          (voltageInVolts setup.initialCapacitorVoltage /
            resistanceInOhms setup.largeCircuitResistance)).const_mul
          (setup.freeSpace.μ₀ *
            lengthInMeters setup.smallLoopVerticalHeight)).div_const
          (2 * Real.pi)).mul_const
        (Real.log
          ((lengthInMeters setup.interCircuitSeparation +
              lengthInMeters setup.smallLoopHorizontalWidth) /
            lengthInMeters setup.interCircuitSeparation)))
  have hFluxDerivative :
      deriv (fluxPerTurnInWebersAtSeconds setup)
          (timeInSeconds setup.observationTime) =
        setup.freeSpace.μ₀ *
            lengthInMeters setup.smallLoopVerticalHeight *
            (voltageInVolts setup.initialCapacitorVoltage /
              resistanceInOhms setup.largeCircuitResistance *
              (Real.exp
                  (-(timeInSeconds setup.observationTime -
                      timeInSeconds setup.switchClosureTime) /
                    (resistanceInOhms setup.largeCircuitResistance *
                      capacitanceInFarads setup.capacitance)) *
                (-(1 : ℝ) /
                  (resistanceInOhms setup.largeCircuitResistance *
                    capacitanceInFarads setup.capacitance)))) /
            (2 * Real.pi) *
            Real.log
              ((lengthInMeters setup.interCircuitSeparation +
                  lengthInMeters setup.smallLoopHorizontalWidth) /
                lengthInMeters setup.interCircuitSeparation) := by
    calc
      deriv (fluxPerTurnInWebersAtSeconds setup)
          (timeInSeconds setup.observationTime) =
          deriv
            (fun seconds =>
              setup.freeSpace.μ₀ *
                lengthInMeters setup.smallLoopVerticalHeight *
                (voltageInVolts setup.initialCapacitorVoltage /
                  resistanceInOhms setup.largeCircuitResistance *
                  Real.exp
                    (-(seconds -
                        timeInSeconds setup.switchClosureTime) /
                      (resistanceInOhms setup.largeCircuitResistance *
                        capacitanceInFarads setup.capacitance))) /
                (2 * Real.pi) *
                Real.log
                  ((lengthInMeters setup.interCircuitSeparation +
                      lengthInMeters setup.smallLoopHorizontalWidth) /
                    lengthInMeters setup.interCircuitSeparation))
            (timeInSeconds setup.observationTime) :=
        hFluxNearObservation.deriv_eq
      _ = _ := hFluxModelDerivative.deriv
  unfold observedSmallCurrentMagnitudeInAmperes
  congr 1
  rw [_ohm.smallCircuitOhmsLaw _ hObservation,
    _faraday.faradayLaw _ hObservation, hFluxDerivative]
  unfold rcStraightWireClosedFormInAmperes
  ring

/-!
At `200 μs`, the induced-current magnitude is the RC/straight-wire closed
form.  Substitution of the literal data gives exactly
`log 3 / (300 * exp 1) A`, approximately `0.001347 A`, which is unequal to
every displayed choice.  The dataset's recorded B remains metadata only.

Blueprint: `thm:physics:phyx_mini_0974:target`.
-/
theorem problem_phyx_mini_0974
    (setup : RCInductionSetup)
    (_figure : MatchesPrimaryCircuitFigure setup)
    (_data : MatchesProblemDescription setup)
    (_physical : HasPhysicalCircuitParameters setup)
    (_timeCoordinate : HasCoherentSecondCoordinate setup)
    (_vacuum : UsesTextbookVacuumPermeability setup)
    (_rc : SatisfiesRCDischargeLaw setup)
    (_field : SatisfiesNearestStraightWireFieldLaw setup)
    (_flux : SatisfiesRectangularStraightWireFluxLaw setup)
    (_faraday : SatisfiesFaradayLaw setup)
    (_wireResistance : SatisfiesSmallWireResistanceLaw setup)
    (_ohm : SatisfiesSmallCircuitOhmsLaw setup) :
    observedSmallCurrentMagnitudeInAmperes setup =
        |rcStraightWireClosedFormInAmperes setup
          (timeInSeconds setup.observationTime)| ∧
      observedSmallCurrentMagnitudeInAmperes setup =
        Real.log 3 / (300 * Real.exp 1) ∧
      (∀ choice : AnswerChoice,
        observedSmallCurrentMagnitudeInAmperes setup ≠
          choice.currentMagnitudeInAmperes) := by
  have hCapacitance :
      capacitanceInFarads setup.capacitance = 1 / 50_000 := by
    have h := _data.capacitanceIsTwentyMicrofarads
    unfold capacitanceInMicrofarads at h
    norm_num at h ⊢
    linarith
  have hSmallWidth :
      lengthInMeters setup.smallLoopHorizontalWidth = 1 / 10 := by
    have h := _data.smallWidthAIsTenCentimeters
    unfold lengthInCentimeters at h
    norm_num at h ⊢
    linarith
  have hSmallHeight :
      lengthInMeters setup.smallLoopVerticalHeight = 1 / 5 := by
    have h := _data.smallHeightBIsTwentyCentimeters
    unfold lengthInCentimeters at h
    norm_num at h ⊢
    linarith
  have hSeparation :
      lengthInMeters setup.interCircuitSeparation = 1 / 20 := by
    have h := _data.separationCIsFiveCentimeters
    unfold lengthInCentimeters at h
    norm_num at h ⊢
    linarith
  have hObservationTime :
      timeInSeconds setup.observationTime = 1 / 5_000 := by
    have h := _data.asksForCurrentAtTwoHundredMicroseconds
    unfold timeInMicroseconds at h
    norm_num at h ⊢
    linarith
  have hTotalWireLength :
      lengthInMeters setup.totalSmallWireLength = 15 := by
    rw [_wireResistance.windingLengthLaw,
      _data.smallCircuitHasTwentyFiveTurns, hSmallWidth, hSmallHeight]
    norm_num
  have hSmallResistance :
      resistanceInOhms setup.smallCircuitResistance = 15 := by
    rw [_wireResistance.resistanceFromWireLength,
      _data.wireResistanceIsOneOhmPerMeter, hTotalWireLength]
    norm_num
  have hClosedFormValue :
      rcStraightWireClosedFormInAmperes setup
          (timeInSeconds setup.observationTime) =
        Real.log 3 / (300 * Real.exp 1) := by
    unfold rcStraightWireClosedFormInAmperes
    rw [_data.smallCircuitHasTwentyFiveTurns,
      _vacuum.vacuumPermeabilityValue, hSmallHeight,
      _data.initialVoltageIsOneHundredVolts, hSeparation, hSmallWidth,
      hObservationTime, _data.switchClosesAtZero, hSmallResistance,
      _data.largeResistanceIsTenOhms, hCapacitance]
    rw [show -(1 / 5_000 - 0) / (10 * (1 / 50_000 : ℝ)) = -1 by
      norm_num]
    rw [Real.exp_neg]
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero]; ring
  have hValuePositive :
      0 < Real.log 3 / (300 * Real.exp 1) := by
    exact div_pos (Real.log_pos (by norm_num))
      (mul_pos (by norm_num) (Real.exp_pos 1))
  have hObservedClosedForm :=
    observedSmallCurrent_eq_closedForm setup _physical _timeCoordinate
      _rc _field _flux _faraday _wireResistance _ohm
  have hObservedValue :
      observedSmallCurrentMagnitudeInAmperes setup =
        Real.log 3 / (300 * Real.exp 1) := by
    calc
      observedSmallCurrentMagnitudeInAmperes setup =
          |rcStraightWireClosedFormInAmperes setup
            (timeInSeconds setup.observationTime)| :=
        hObservedClosedForm
      _ = |Real.log 3 / (300 * Real.exp 1)| := by
        rw [hClosedFormValue]
      _ = Real.log 3 / (300 * Real.exp 1) :=
        abs_of_pos hValuePositive
  refine ⟨hObservedClosedForm, hObservedValue, ?_⟩
  have hLogUpper : Real.log 3 < 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hExpLower : 1 ≤ Real.exp 1 :=
    Real.one_le_exp (by norm_num)
  have hValueUpper :
      Real.log 3 / (300 * Real.exp 1) < 1 / 100 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) (Real.exp_pos 1))).2
    nlinarith
  intro choice hChoice
  have hChoiceLower :
      (1 / 100 : ℝ) < choice.currentMagnitudeInAmperes := by
    cases choice <;> norm_num [AnswerChoice.currentMagnitudeInAmperes]
  rw [hObservedValue] at hChoice
  linarith

end PhyXMiniProblems.ProblemPhyXMini0974
