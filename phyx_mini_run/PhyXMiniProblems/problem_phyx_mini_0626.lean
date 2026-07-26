import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0626

open Dimension

/-!
# Conduction electrons per silicon atom from the Hall effect

A silicon strip carries an in-plane current while a magnetic field is applied
normal to the strip.  The measured Hall voltage determines the conduction-
electron number density.  The bulk mass density and the mass of a silicon atom
determine the silicon-atom number density, and their ratio is the requested
number of conduction electrons per atom.

Physical lengths, current, magnetic flux density, voltage magnitude, charge,
mass, mass density, and number densities are represented by Physlib
`Dimensionful` quantities.  Real scalars below are only calibrated unit
readouts, dimensionless ratios, reference constants in explicitly named units,
schematic directions, and displayed multiple-choice values.
-/

/-! ## Physical dimensions and quantities -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Energy in the MLTQ dimension system. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension mass per charge per time. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * C𝓭⁻¹ * T𝓭⁻¹

/-- Bulk mass density has dimension mass per volume. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- Particle number density has dimension inverse volume. -/
def numberDensityDimension : Dimension :=
  L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical electric-current magnitude. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative physical Hall-voltage magnitude. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative physical magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative physical charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical bulk mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical particle number density. -/
abbrev NumberDensityQuantity : Type :=
  Dimensionful (WithDim numberDensityDimension NNReal)

/-- A direction vector in physical three-space. -/
abbrev SpatialDirection : Type := EuclideanSpace ℝ (Fin 3)

/-! ## Calibrated unit readouts -/

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Electric-current readout in amperes (`coulomb / second`). -/
def electricCurrentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Electric-current readout in milliamperes. -/
def electricCurrentInMilliamperes (current : ElectricCurrentQuantity) : ℝ :=
  1000 * electricCurrentInAmperes current

/-- Hall-voltage-magnitude readout in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  nonnegativeSIReadout potential

/-- Hall-voltage-magnitude readout in millivolts. -/
def electricPotentialInMillivolts (potential : ElectricPotentialQuantity) : ℝ :=
  1000 * electricPotentialInVolts potential

/-- Magnetic-flux-density readout in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Charge-magnitude readout in units of Physlib's elementary charge. -/
def chargeMagnitudeInElementaryCharges
    (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with
      charge := ChargeUnit.elementaryCharge}).val : ℝ)

/-- Mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Bulk-mass-density readout in kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Particle-number-density readout in particles per cubic metre. -/
def numberDensityPerCubicMeter (density : NumberDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-! ## Figure vocabulary and physical setup -/

/-- The two vector labels visible in the supplied image. -/
inductive FigureVector where
  | currentI
  | magneticFieldB
  deriving DecidableEq, Fintype, Repr

/-- The visible color of a vector arrow in the supplied image. -/
inductive FigureArrowColor where
  | black
  | blue
  deriving DecidableEq, Repr

/-- Primary-image information from `626.png`. -/
structure HallStripFigure where
  printedLabel : FigureVector → String
  arrowColor : FigureVector → FigureArrowColor
  currentArrowLiesInStripPlane : Bool
  currentArrowPointsTowardLowerLeft : Bool
  magneticFieldArrowIsNormalToStrip : Bool
  magneticFieldArrowPointsAwayFromStrip : Bool

/-!
The physical silicon-strip experiment.  The requested carrier ratio is an
independent dimensionless observable; it is not defined from an answer choice
or from the numerical result to be shown.
-/
structure SiliconHallSetup where
  stripWidth : LengthQuantity
  stripThickness : LengthQuantity
  appliedMagneticFluxDensity : MagneticFluxDensityQuantity
  currentMagnitude : ElectricCurrentQuantity
  hallVoltageMagnitude : ElectricPotentialQuantity
  siliconBulkMassDensity : MassDensityQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  siliconAtomMass : MassQuantity
  conductionElectronNumberDensity : NumberDensityQuantity
  siliconAtomNumberDensity : NumberDensityQuantity
  conductionElectronsPerSiliconAtom : ℝ
  siliconMolarMassKilogramsPerMole : ℝ
  avogadroConstantPerMole : ℝ
  currentDirection : SpatialDirection
  magneticFieldDirection : SpatialDirection
  stripNormalDirection : SpatialDirection
  figure : HallStripFigure

/-! ## Scenario, figure, and numerical readouts -/

/-- Qualitative geometry and positivity conditions of the Hall experiment. -/
structure MatchesSiliconHallScenario (setup : SiliconHallSetup) : Prop where
  stripHasPositiveWidth :
    0 < lengthReadout LengthUnit.meters setup.stripWidth
  stripHasPositiveThickness :
    0 < lengthReadout LengthUnit.meters setup.stripThickness
  currentIsNonzero :
    0 < electricCurrentInAmperes setup.currentMagnitude
  fieldIsNonzero :
    0 < magneticFluxDensityInTeslas setup.appliedMagneticFluxDensity
  hallVoltageIsNonzero :
    0 < electricPotentialInVolts setup.hallVoltageMagnitude
  currentDirectionIsNonzero : setup.currentDirection ≠ 0
  magneticFieldDirectionIsNonzero : setup.magneticFieldDirection ≠ 0
  stripNormalIsNonzero : setup.stripNormalDirection ≠ 0
  currentLiesInStripPlane :
    inner ℝ setup.currentDirection setup.stripNormalDirection = 0
  magneticFieldIsNormalToStrip :
    ∃ scale : ℝ, scale ≠ 0 ∧
      setup.magneticFieldDirection = scale • setup.stripNormalDirection
  currentAndFieldArePerpendicular :
    inner ℝ setup.currentDirection setup.magneticFieldDirection = 0
  carrierRatioIsNonnegative :
    0 ≤ setup.conductionElectronsPerSiliconAtom
  electronDensityIsPositive :
    0 < numberDensityPerCubicMeter setup.conductionElectronNumberDensity
  atomDensityIsPositive :
    0 < numberDensityPerCubicMeter setup.siliconAtomNumberDensity

/-- Labels, colors, and arrow geometry read directly from the supplied image. -/
structure MatchesSuppliedHallStripFigure (figure : HallStripFigure) : Prop where
  currentLabel : figure.printedLabel .currentI = "I"
  magneticFieldLabel : figure.printedLabel .magneticFieldB = "B"
  currentArrowIsBlack : figure.arrowColor .currentI = .black
  magneticFieldArrowIsBlue : figure.arrowColor .magneticFieldB = .blue
  currentShownInPlane : figure.currentArrowLiesInStripPlane = true
  currentShownTowardLowerLeft :
    figure.currentArrowPointsTowardLowerLeft = true
  fieldShownNormalToStrip :
    figure.magneticFieldArrowIsNormalToStrip = true
  fieldShownPointingAway :
    figure.magneticFieldArrowPointsAwayFromStrip = true

/-- Measured dimensions and electromagnetic readouts stated in the problem. -/
structure MatchesProblemMeasurements (setup : SiliconHallSetup) : Prop where
  widthInCentimeters :
    lengthReadout LengthUnit.centimeters setup.stripWidth = 8 / 5
  thicknessInMillimeters :
    lengthReadout LengthUnit.millimeters setup.stripThickness = 1
  magneticFieldInTeslas :
    magneticFluxDensityInTeslas setup.appliedMagneticFluxDensity = 3 / 2
  currentInMilliamperes :
    electricCurrentInMilliamperes setup.currentMagnitude = 7 / 25
  hallVoltageInMillivolts :
    electricPotentialInMillivolts setup.hallVoltageMagnitude = 18
  massDensityInSI :
    massDensityInKilogramsPerCubicMeter setup.siliconBulkMassDensity = 2330

/-!
Reference atomic data needed to convert the stated silicon mass density to an
atom number density.  These are calibrated data readouts, not the requested
conduction-electron ratio.
-/
structure MatchesSiliconAtomicReferenceData (setup : SiliconHallSetup) : Prop where
  carrierChargeIsOneElementaryCharge :
    chargeMagnitudeInElementaryCharges setup.electronChargeMagnitude = 1
  siliconMolarMass :
    setup.siliconMolarMassKilogramsPerMole = 56_171 / 2_000_000
  avogadroConstant :
    setup.avogadroConstantPerMole = 602_214_076_000_000_000_000_000

/-! ## Governing physical laws -/

/-!
Magnitude form of the Hall-effect law
`V_H q n t = I B` for a rectangular strip.  The width is part of the physical
setup but cancels when current density is converted back to total current.
-/
structure SatisfiesHallEffectLaw (setup : SiliconHallSetup) : Prop where
  hallVoltageRelation :
    electricPotentialInVolts setup.hallVoltageMagnitude *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          numberDensityPerCubicMeter setup.conductionElectronNumberDensity *
          lengthReadout LengthUnit.meters setup.stripThickness =
      electricCurrentInAmperes setup.currentMagnitude *
        magneticFluxDensityInTeslas setup.appliedMagneticFluxDensity

/-!
The mass of one silicon atom is molar mass divided by Avogadro's constant, and
bulk mass density is atom number density times mass per atom.
-/
structure SatisfiesSiliconAtomicDensityLaw (setup : SiliconHallSetup) : Prop where
  atomMassFromMolarMass :
    massInKilograms setup.siliconAtomMass * setup.avogadroConstantPerMole =
      setup.siliconMolarMassKilogramsPerMole
  bulkDensityFromAtoms :
    numberDensityPerCubicMeter setup.siliconAtomNumberDensity *
        massInKilograms setup.siliconAtomMass =
      massDensityInKilogramsPerCubicMeter setup.siliconBulkMassDensity

/-!
The dimensionless number of conduction electrons per atom converts silicon-
atom number density to conduction-electron number density.  This is a general
balance law and does not assert the requested numerical answer.
-/
structure SatisfiesCarrierPerAtomBalance (setup : SiliconHallSetup) : Prop where
  carrierDensityFromRatio :
    setup.conductionElectronsPerSiliconAtom *
        numberDensityPerCubicMeter setup.siliconAtomNumberDensity =
      numberDensityPerCubicMeter setup.conductionElectronNumberDensity

/-! ## Multiple-choice target -/

/-- The four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless displayed value of an answer choice. -/
def AnswerChoice.displayedValue : AnswerChoice → ℝ
  | .A => 39 / 10_000_000_000
  | .B => 29 / 1_000_000_000
  | .C => 2 / 1_000_000_000
  | .D => 29 / 10_000_000_000

/-- A choice is at least as close to the physical value as every other choice. -/
def IsClosestAnswer (value : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |value - choice.displayedValue| ≤ |value - other.displayedValue|

/-- A value rounds to a displayed center at the given decimal step. -/
def RoundsToDisplayedValue (value center decimalStep : ℝ) : Prop :=
  |value - center| ≤ decimalStep / 2

/-!
The Hall and atomic-density laws imply approximately `2.9 × 10⁻⁹`
conduction electrons per silicon atom, so the recorded answer D is closest.

Blueprint label: `thm:physics:phyx_mini_0626:target`.
-/
theorem conductionElectronsPerSiliconAtom_is_answer_D
    (setup : SiliconHallSetup)
    (_scenario : MatchesSiliconHallScenario setup)
    (_figure : MatchesSuppliedHallStripFigure setup.figure)
    (_measurements : MatchesProblemMeasurements setup)
    (_atomicData : MatchesSiliconAtomicReferenceData setup)
    (_hallLaw : SatisfiesHallEffectLaw setup)
    (_atomicDensityLaw : SatisfiesSiliconAtomicDensityLaw setup)
    (_carrierBalance : SatisfiesCarrierPerAtomBalance setup) :
    IsClosestAnswer setup.conductionElectronsPerSiliconAtom .D ∧
      RoundsToDisplayedValue
        setup.conductionElectronsPerSiliconAtom
        AnswerChoice.D.displayedValue
        (1 / 10_000_000_000) := by
  have millimeters_eq_thousand_meters (length : LengthQuantity) :
      lengthReadout LengthUnit.millimeters length =
        1000 * lengthReadout LengthUnit.meters length := by
    have hunit := length.2
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.millimeters} : UnitChoices)
    have hval :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hunit
    norm_num [lengthReadout, UnitChoices.dimScale, LengthUnit.meters,
      LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def] at hval ⊢
    exact hval
  have charge_conversion (charge : ChargeMagnitudeQuantity) :
      chargeMagnitudeInCoulombs charge =
        1.602176634e-19 * chargeMagnitudeInElementaryCharges charge := by
    have hscale :
        ({UnitChoices.SI with charge := ChargeUnit.elementaryCharge} :
            UnitChoices).dimScale UnitChoices.SI C𝓭 =
          (1.602176634e-19 : NNReal) := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale_apply, ChargeUnit.elementaryCharge,
        ChargeUnit.coulombs, ChargeUnit.scale, ChargeUnit.div_eq_val, C𝓭]
      change
        ((801088317 / 5000000000000000000000000000 : NNReal) : ℝ) =
          (801088317 / 5000000000000000000000000000 : ℝ)
      norm_num
    have h :=
      congrArg (fun x : WithDim C𝓭 NNReal => (x.val : ℝ))
      (charge.property
        {UnitChoices.SI with charge := ChargeUnit.elementaryCharge}
        UnitChoices.SI)
    simp only [WithDim.dim_apply] at h
    rw [hscale] at h
    norm_num [chargeMagnitudeInCoulombs, nonnegativeSIReadout,
      chargeMagnitudeInElementaryCharges, NNReal.smul_def] at h ⊢
    exact h
  have hcurrent :
      electricCurrentInAmperes setup.currentMagnitude = 7 / 25_000 := by
    have h := _measurements.currentInMilliamperes
    norm_num [electricCurrentInMilliamperes] at h ⊢
    linarith
  have hvoltage :
      electricPotentialInVolts setup.hallVoltageMagnitude = 9 / 500 := by
    have h := _measurements.hallVoltageInMillivolts
    norm_num [electricPotentialInMillivolts] at h ⊢
    linarith
  have hthickness :
      lengthReadout LengthUnit.meters setup.stripThickness = 1 / 1000 := by
    have h := _measurements.thicknessInMillimeters
    rw [millimeters_eq_thousand_meters] at h
    norm_num at h ⊢
    linarith
  have hcharge :
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
        1.602176634e-19 := by
    rw [charge_conversion,
      _atomicData.carrierChargeIsOneElementaryCharge]
    norm_num
  have havogadro_pos : 0 < setup.avogadroConstantPerMole := by
    rw [_atomicData.avogadroConstant]
    norm_num
  have hatomMass :
      massInKilograms setup.siliconAtomMass =
        setup.siliconMolarMassKilogramsPerMole /
          setup.avogadroConstantPerMole :=
    (eq_div_iff (ne_of_gt havogadro_pos)).2
      _atomicDensityLaw.atomMassFromMolarMass
  have hatomMass_pos :
      0 < massInKilograms setup.siliconAtomMass := by
    rw [hatomMass, _atomicData.siliconMolarMass,
      _atomicData.avogadroConstant]
    norm_num
  have hatomDensity :
      numberDensityPerCubicMeter setup.siliconAtomNumberDensity =
        massDensityInKilogramsPerCubicMeter setup.siliconBulkMassDensity /
          massInKilograms setup.siliconAtomMass :=
    (eq_div_iff (ne_of_gt hatomMass_pos)).2
      _atomicDensityLaw.bulkDensityFromAtoms
  have hhallCoefficient_pos :
      0 <
        electricPotentialInVolts setup.hallVoltageMagnitude *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          lengthReadout LengthUnit.meters setup.stripThickness := by
    rw [hvoltage, hcharge, hthickness]
    norm_num
  have hhallRearranged :
      (electricPotentialInVolts setup.hallVoltageMagnitude *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          lengthReadout LengthUnit.meters setup.stripThickness) *
          numberDensityPerCubicMeter setup.conductionElectronNumberDensity =
        electricCurrentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas
            setup.appliedMagneticFluxDensity := by
    calc
      _ = electricPotentialInVolts setup.hallVoltageMagnitude *
            chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
            numberDensityPerCubicMeter
              setup.conductionElectronNumberDensity *
            lengthReadout LengthUnit.meters setup.stripThickness := by ring
      _ = _ := _hallLaw.hallVoltageRelation
  have helectronDensity :
      numberDensityPerCubicMeter setup.conductionElectronNumberDensity =
        (electricCurrentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas
              setup.appliedMagneticFluxDensity) /
          (electricPotentialInVolts setup.hallVoltageMagnitude *
            chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
            lengthReadout LengthUnit.meters setup.stripThickness) :=
    (eq_div_iff (ne_of_gt hhallCoefficient_pos)).2
      (by simpa [mul_comm] using hhallRearranged)
  have hatomDensity_pos :
      0 < numberDensityPerCubicMeter setup.siliconAtomNumberDensity :=
    _scenario.atomDensityIsPositive
  have hratio :
      setup.conductionElectronsPerSiliconAtom =
        numberDensityPerCubicMeter
            setup.conductionElectronNumberDensity /
          numberDensityPerCubicMeter setup.siliconAtomNumberDensity :=
    (eq_div_iff (ne_of_gt hatomDensity_pos)).2
      _carrierBalance.carrierDensityFromRatio
  have hratio_exact :
      setup.conductionElectronsPerSiliconAtom =
        (((7 / 25_000 : ℝ) * (3 / 2)) /
            ((9 / 500) * (1.602176634e-19) * (1 / 1000))) /
          (2330 /
            ((56_171 / 2_000_000) /
              602_214_076_000_000_000_000_000)) := by
    rw [hratio, helectronDensity, hatomDensity, hatomMass, hcurrent,
      _measurements.magneticFieldInTeslas, hvoltage, hcharge, hthickness,
      _measurements.massDensityInSI, _atomicData.siliconMolarMass,
      _atomicData.avogadroConstant]
  constructor
  · intro other
    cases other <;>
      norm_num [IsClosestAnswer, AnswerChoice.displayedValue, hratio_exact,
        abs_of_nonneg, abs_of_nonpos]
  · norm_num [RoundsToDisplayedValue, AnswerChoice.displayedValue,
      hratio_exact, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0626
