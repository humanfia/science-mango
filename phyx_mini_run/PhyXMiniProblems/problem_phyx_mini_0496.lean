import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/-!
# PhyX mini problem 0496: undeflected proton between parallel electrodes

A proton enters midway between two parallel electrodes, travels to the right,
and, with only the electric field present, strikes the far end of the lower
electrode.  That trajectory determines its speed.  The requested perpendicular
magnetic field then cancels the transverse electric force.

Lengths, time, mass, charge, speed, voltage, and field strengths are represented
by Physlib dimensionful quantities.  Numerical equations are stated using their
SI readouts.  The spacetime-dependent fields themselves use Physlib's
`Electromagnetism.ElectricField` and `Electromagnetism.MagneticField` types.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0496

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative elapsed time. -/
abbrev TimeIntervalQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type := Dimensionful (WithDim C𝓭 NNReal)

/-- The physical dimension `L T⁻¹` of speed. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `M L² T⁻² C⁻¹` of potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic-field strength. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- A nonnegative electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative magnetic-field magnitude. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-- SI length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- SI elapsed-time readout in seconds. -/
def timeInSeconds (time : TimeIntervalQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- SI mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- SI charge-magnitude readout in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- SI speed readout in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- SI potential-difference readout in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-- SI electric-field-strength readout in volts per metre. -/
def electricFieldStrengthInVoltsPerMeter
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI magnetic-field-strength readout in teslas. -/
def magneticFieldStrengthInTeslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Magnetic-field-strength readout in milliteslas. -/
def magneticFieldStrengthInMilliteslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  1000 * magneticFieldStrengthInTeslas strength

/-! ## Physical and figure labels -/

/-- Charged-particle species distinguished by the model. -/
inductive ParticleSpecies where
  | proton
  | other
  deriving DecidableEq, Repr

/-- The upper and lower electrode labels from the supplied figure. -/
inductive ElectrodeLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Whether the long electrodes have the parallel geometry shown. -/
inductive ElectrodeArrangement where
  | parallel
  | nonparallel
  deriving DecidableEq, Repr

/-- Named directions used in the side-view diagram. -/
inductive SpatialDirection where
  | right
  | left
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/--
Physical quantities and diagrammatic observables for the experiment.

The magnetic strength is an independent physical observable.  Its requested
numerical value is not stored here and is constrained only by the general laws
below.
-/
structure ParallelPlateProtonSetup where
  particleSpecies : ParticleSpecies
  electrodeArrangement : ElectrodeArrangement
  electrodeLength : LengthQuantity
  electrodeSeparation : LengthQuantity
  entryHeightAboveLowerElectrode : LengthQuantity
  potentialDifference : PotentialDifferenceQuantity
  particleMass : MassQuantity
  particleChargeMagnitude : ChargeMagnitudeQuantity
  initialHorizontalSpeed : SpeedQuantity
  electricOnlyTransitTime : TimeIntervalQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  magneticFieldStrength : MagneticFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 3
  magneticField : Electromagnetism.MagneticField 3
  betweenElectrodes : Set (Time × Space 3)
  velocityDirection : SpatialDirection
  electricFieldDirection : SpatialDirection
  magneticFieldDirection : SpatialDirection
  electricOnlyImpactPlate : ElectrodeLabel
  electricOnlyImpactHorizontalDistance : LengthQuantity
  electricOnlyVerticalDeflectionMagnitude : LengthQuantity

/-! ## Problem, figure, and calibration readouts -/

/--
Numerical and qualitative data supplied by the problem and primary image.

The `0.005 m` entry height records that the proton starts equally far from the
plates.  The impact fields record the electric-only trajectory reaching the
outer end of the lower electrode.  No magnetic answer value occurs here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : ParallelPlateProtonSetup) : Prop where
  particleIsProton : setup.particleSpecies = .proton
  platesAreParallel : setup.electrodeArrangement = .parallel
  electrodeLengthReadout : lengthInMeters setup.electrodeLength = 5 / 100
  electrodeSeparationReadout :
    lengthInMeters setup.electrodeSeparation = 1 / 100
  centeredEntryReadout :
    lengthInMeters setup.entryHeightAboveLowerElectrode = 1 / 200
  entryIsMidway :
    lengthInMeters setup.entryHeightAboveLowerElectrode =
      lengthInMeters setup.electrodeSeparation / 2
  potentialDifferenceReadout :
    potentialDifferenceInVolts setup.potentialDifference = 500
  entersFromLeft : setup.velocityDirection = .right
  electricDeflectionIsDownward : setup.electricFieldDirection = .downward
  impactsLowerElectrode : setup.electricOnlyImpactPlate = .lower
  impactsAtOuterEnd :
    lengthInMeters setup.electricOnlyImpactHorizontalDistance =
      lengthInMeters setup.electrodeLength
  impactDeflectionReadout :
    lengthInMeters setup.electricOnlyVerticalDeflectionMagnitude =
      lengthInMeters setup.entryHeightAboveLowerElectrode

/--
Standard proton mass and elementary-charge readouts used for evaluating the
multiple-choice result.  These are calibration data, not the requested field.
-/
structure HasStandardProtonCalibration
    (setup : ParallelPlateProtonSetup) : Prop where
  protonMassReadout :
    massInKilograms setup.particleMass =
      (167262192595 / 10 ^ 38 : ℝ)
  protonChargeReadout :
    chargeInCoulombs setup.particleChargeMagnitude =
      (1602176634 / 10 ^ 28 : ℝ)

/-- Positivity and non-vacuity conditions for the physical experiment. -/
structure HasPhysicalParameters
    (setup : ParallelPlateProtonSetup) : Prop where
  electrodeLengthPositive : 0 < lengthInMeters setup.electrodeLength
  electrodeSeparationPositive : 0 < lengthInMeters setup.electrodeSeparation
  particleMassPositive : 0 < massInKilograms setup.particleMass
  particleChargePositive : 0 < chargeInCoulombs setup.particleChargeMagnitude
  speedPositive : 0 < speedInMetersPerSecond setup.initialHorizontalSpeed
  transitTimePositive : 0 < timeInSeconds setup.electricOnlyTransitTime
  electricStrengthPositive :
    0 < electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength
  magneticStrengthPositive :
    0 < magneticFieldStrengthInTeslas setup.magneticFieldStrength
  plateGapRegionNonempty : setup.betweenElectrodes.Nonempty

/-! ## Field geometry and governing laws -/

/-- A spacetime-dependent vector field vanishes outside the specified region. -/
def FieldIsConfinedTo
    (region : Set (Time × Space 3))
    (field : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ time position, (time, position) ∉ region → field time position = 0

/-- Both applied fields are confined to the gap between the electrodes. -/
structure FieldsAreConfinedToPlateGap
    (setup : ParallelPlateProtonSetup) : Prop where
  electricFieldConfined :
    FieldIsConfinedTo setup.betweenElectrodes setup.electricField
  magneticFieldConfined :
    FieldIsConfinedTo setup.betweenElectrodes setup.magneticField

/--
The dimensionful scalar strengths are the uniform magnitudes of the Physlib
vector fields throughout the plate gap.
-/
structure FieldsHaveUniformMagnitudeInPlateGap
    (setup : ParallelPlateProtonSetup) : Prop where
  electricMagnitude :
    ∀ time position, (time, position) ∈ setup.betweenElectrodes →
      ‖setup.electricField time position‖ =
        electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength
  magneticMagnitude :
    ∀ time position, (time, position) ∈ setup.betweenElectrodes →
      ‖setup.magneticField time position‖ =
        magneticFieldStrengthInTeslas setup.magneticFieldStrength

/-- Uniform parallel-plate electrostatics: `E = ΔV / d`. -/
def SatisfiesParallelPlateElectricFieldLaw
    (setup : ParallelPlateProtonSetup) : Prop :=
  electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength =
    potentialDifferenceInVolts setup.potentialDifference /
      lengthInMeters setup.electrodeSeparation

/--
Horizontal uniform motion and downward constant-acceleration motion during the
electric-only traversal.  The vertical equation is
`y = (1/2) (q E / m) t²`, with zero initial vertical velocity.
-/
structure SatisfiesElectricOnlyDeflectionKinematics
    (setup : ParallelPlateProtonSetup) : Prop where
  horizontalMotion :
    lengthInMeters setup.electricOnlyImpactHorizontalDistance =
      speedInMetersPerSecond setup.initialHorizontalSpeed *
        timeInSeconds setup.electricOnlyTransitTime
  verticalMotion :
    lengthInMeters setup.electricOnlyVerticalDeflectionMagnitude =
      (1 / 2 : ℝ) *
        (chargeInCoulombs setup.particleChargeMagnitude *
            electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength /
          massInKilograms setup.particleMass) *
        timeInSeconds setup.electricOnlyTransitTime ^ 2

/--
For a right-moving positive proton and a field into the page, the upward
magnetic force cancels the downward electric force.  The transverse Lorentz
force balance is `q E = q v B`; it contains no numerical answer for `B`.
-/
structure SatisfiesUndeflectedLorentzForceBalance
    (setup : ParallelPlateProtonSetup) : Prop where
  rightMovingProton : setup.velocityDirection = .right
  electricForceDownward : setup.electricFieldDirection = .downward
  magneticFieldIntoPage : setup.magneticFieldDirection = .intoPage
  zeroNetTransverseForce :
    chargeInCoulombs setup.particleChargeMagnitude *
        electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength =
      chargeInCoulombs setup.particleChargeMagnitude *
        speedInMetersPerSecond setup.initialHorizontalSpeed *
          magneticFieldStrengthInTeslas setup.magneticFieldStrength

/-! ## Answer readouts and formalization targets -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Magnetic strength in milliteslas displayed by an answer choice. -/
def answerStrengthInMilliteslas : AnswerChoice → ℝ
  | .A => 49
  | .B => 23
  | .C => 46
  | .D => 56

/-- The physical strength is within half a millitesla of a whole-mT readout. -/
def RoundsToNearestWholeMillitesla
    (setup : ParallelPlateProtonSetup) (reading : ℝ) : Prop :=
  |magneticFieldStrengthInMilliteslas setup.magneticFieldStrength - reading| ≤
    1 / 2

/-- A displayed answer is at least as close as every other displayed answer. -/
def IsClosestDisplayedChoice
    (setup : ParallelPlateProtonSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    |magneticFieldStrengthInMilliteslas setup.magneticFieldStrength -
        answerStrengthInMilliteslas choice| ≤
      |magneticFieldStrengthInMilliteslas setup.magneticFieldStrength -
        answerStrengthInMilliteslas otherChoice|

/-- The `500 V` across `1.0 cm` plates gives `50000 V/m`. -/
lemma electricFieldStrength_eq_fiftyThousand_voltsPerMeter
    (setup : ParallelPlateProtonSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hElectricField : SatisfiesParallelPlateElectricFieldLaw setup) :
    electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength = 50000 := by
  rw [hElectricField, hData.potentialDifferenceReadout,
    hData.electrodeSeparationReadout]
  norm_num

/--
Eliminating transit time and speed from the electric trajectory and Lorentz
balance gives `B = sqrt (m ΔV / q) / L`.
-/
lemma requiredMagneticField_exactFormula
    (setup : ParallelPlateProtonSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hElectricField : SatisfiesParallelPlateElectricFieldLaw setup)
    (hKinematics : SatisfiesElectricOnlyDeflectionKinematics setup)
    (hLorentz : SatisfiesUndeflectedLorentzForceBalance setup) :
    magneticFieldStrengthInTeslas setup.magneticFieldStrength =
      Real.sqrt
          (massInKilograms setup.particleMass *
            potentialDifferenceInVolts setup.potentialDifference /
            chargeInCoulombs setup.particleChargeMagnitude) /
        lengthInMeters setup.electrodeLength := by
  have hE :=
    electricFieldStrength_eq_fiftyThousand_voltsPerMeter
      setup hData hElectricField
  have hHorizontal := hKinematics.horizontalMotion
  rw [hData.impactsAtOuterEnd, hData.electrodeLengthReadout] at hHorizontal
  have hVertical := hKinematics.verticalMotion
  rw [hData.impactDeflectionReadout, hData.centeredEntryReadout, hE] at hVertical
  field_simp [ne_of_gt hPhysical.particleMassPositive] at hVertical
  have hForce := hLorentz.zeroNetTransverseForce
  rw [hE] at hForce
  have hSpeedField :
      speedInMetersPerSecond setup.initialHorizontalSpeed *
          magneticFieldStrengthInTeslas setup.magneticFieldStrength =
        50000 := by
    nlinarith [hPhysical.particleChargePositive]
  have hFieldTime :
      magneticFieldStrengthInTeslas setup.magneticFieldStrength =
        1000000 * timeInSeconds setup.electricOnlyTransitTime := by
    nlinarith [hPhysical.speedPositive]
  have hRadicand :
      massInKilograms setup.particleMass * 500 /
          chargeInCoulombs setup.particleChargeMagnitude =
        (50000 * timeInSeconds setup.electricOnlyTransitTime) ^ 2 := by
    field_simp [ne_of_gt hPhysical.particleChargePositive]
    nlinarith
  have hSqrt :
      Real.sqrt
          (massInKilograms setup.particleMass * 500 /
            chargeInCoulombs setup.particleChargeMagnitude) =
        50000 * timeInSeconds setup.electricOnlyTransitTime := by
    rw [hRadicand, Real.sqrt_sq]
    nlinarith [hPhysical.transitTimePositive]
  rw [hData.potentialDifferenceReadout, hData.electrodeLengthReadout, hSqrt]
  nlinarith

/-- The calibrated exact result lies between `45.5 mT` and `46.5 mT`. -/
lemma requiredMagneticField_milliteslaBounds
    (setup : ParallelPlateProtonSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hCalibration : HasStandardProtonCalibration setup)
    (hPhysical : HasPhysicalParameters setup)
    (hElectricField : SatisfiesParallelPlateElectricFieldLaw setup)
    (hKinematics : SatisfiesElectricOnlyDeflectionKinematics setup)
    (hLorentz : SatisfiesUndeflectedLorentzForceBalance setup) :
    (91 / 2 : ℝ) <
        magneticFieldStrengthInMilliteslas setup.magneticFieldStrength ∧
      magneticFieldStrengthInMilliteslas setup.magneticFieldStrength <
        (93 / 2 : ℝ) := by
  have hExact :=
    requiredMagneticField_exactFormula
      setup hData hPhysical hElectricField hKinematics hLorentz
  have hLower :
      (91 / 40000 : ℝ) <
        Real.sqrt
          ((167262192595 / 10 ^ 38 : ℝ) * 500 /
            (1602176634 / 10 ^ 28 : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hUpper :
      Real.sqrt
          ((167262192595 / 10 ^ 38 : ℝ) * 500 /
            (1602176634 / 10 ^ 28 : ℝ)) <
        (93 / 40000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  unfold magneticFieldStrengthInMilliteslas
  rw [hExact, hCalibration.protonMassReadout,
    hCalibration.protonChargeReadout, hData.potentialDifferenceReadout,
    hData.electrodeLengthReadout]
  constructor <;> nlinarith

/--
The magnetic field that permits undeflected passage rounds to `46 mT`, which
is the closest displayed strength and therefore answer C.

This declaration formalizes `thm:physics:phyx_mini_0496:target`.
-/
theorem problem_phyx_mini_0496
    (setup : ParallelPlateProtonSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hCalibration : HasStandardProtonCalibration setup)
    (hPhysical : HasPhysicalParameters setup)
    (hConfined : FieldsAreConfinedToPlateGap setup)
    (hUniform : FieldsHaveUniformMagnitudeInPlateGap setup)
    (hElectricField : SatisfiesParallelPlateElectricFieldLaw setup)
    (hKinematics : SatisfiesElectricOnlyDeflectionKinematics setup)
    (hLorentz : SatisfiesUndeflectedLorentzForceBalance setup) :
    RoundsToNearestWholeMillitesla setup
        (answerStrengthInMilliteslas .C) ∧
      IsClosestDisplayedChoice setup .C := by
  have hBounds :=
    requiredMagneticField_milliteslaBounds
      setup hData hCalibration hPhysical hElectricField hKinematics hLorentz
  have hRound :
      |magneticFieldStrengthInMilliteslas setup.magneticFieldStrength - 46| ≤
        (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hBounds.1, hBounds.2]
  constructor
  · simpa [RoundsToNearestWholeMillitesla,
      answerStrengthInMilliteslas] using hRound
  · unfold IsClosestDisplayedChoice
    intro otherChoice
    cases otherChoice with
    | A =>
        simp only [answerStrengthInMilliteslas]
        calc
          |magneticFieldStrengthInMilliteslas
                setup.magneticFieldStrength - 46| ≤ (1 / 2 : ℝ) := hRound
          _ ≤
              |magneticFieldStrengthInMilliteslas
                  setup.magneticFieldStrength - 49| := by
            rw [abs_of_nonpos (by nlinarith [hBounds.2])]
            nlinarith
    | B =>
        simp only [answerStrengthInMilliteslas]
        calc
          |magneticFieldStrengthInMilliteslas
                setup.magneticFieldStrength - 46| ≤ (1 / 2 : ℝ) := hRound
          _ ≤
              |magneticFieldStrengthInMilliteslas
                  setup.magneticFieldStrength - 23| := by
            rw [abs_of_nonneg (by nlinarith [hBounds.1])]
            nlinarith
    | C =>
        simp only [answerStrengthInMilliteslas]
        exact le_rfl
    | D =>
        simp only [answerStrengthInMilliteslas]
        calc
          |magneticFieldStrengthInMilliteslas
                setup.magneticFieldStrength - 46| ≤ (1 / 2 : ℝ) := hRound
          _ ≤
              |magneticFieldStrengthInMilliteslas
                  setup.magneticFieldStrength - 56| := by
            rw [abs_of_nonpos (by nlinarith [hBounds.2])]
            nlinarith

end PhyXMiniProblems.ProblemPhyXMini0496
