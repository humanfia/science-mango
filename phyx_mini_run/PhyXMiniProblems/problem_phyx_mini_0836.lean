import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0836

open Dimension

/-!
# Electric field from an electron's parabolic path

An electron leaves the positive lower plate of a parallel-plate capacitor at
`45°` with speed `5.0 * 10^6 m/s`.  Under the upward electric field, its
negative charge gives it a constant downward acceleration, and it returns to
the lower plate `4.0 cm` to the right.

The physical speed, range, plate separation, flight time, mass, charge
magnitude, acceleration, and electric-field strength are unit-independent
Physlib quantities.  Real numbers appear only as explicit unit readouts,
dimensionless angles, and displayed numerical answers.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- Acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric-field strength has dimension force divided by charge. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Read a physical length in a selected named unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected named unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a physical mass in a selected named unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read an electric-charge magnitude in a selected named unit. -/
def chargeReadout
    (unit : ChargeUnit) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with charge := unit}).val : ℝ)

/-- Read an acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Coherent-SI readout of an electric-field strength, in newtons/coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the figure's `4.0 cm` label. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Coulomb readout of an electric-charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-!
Physlib's elementary-charge unit expressed as a scalar number of coulombs.
The electron charge in the setup remains a dimensionful physical quantity.
-/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- CODATA electron rest-mass readout used by the model, in kilograms. -/
def electronRestMassInKilograms : ℝ :=
  (9.1093837139 : ℝ) * 10 ^ (-31 : ℤ)

/-! ## Apparatus, directions, and primary-figure content -/

/-- Particle species distinguished by the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Sign of a particle's electric charge. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The two horizontal capacitor plates in the raster figure. -/
inductive PlateLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Electrical polarity shown by the marks on a plate. -/
inductive PlatePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Relative geometry of the two capacitor plates. -/
inductive PlateArrangement where
  | parallel
  | nonparallel
  deriving DecidableEq, Repr

/-- Directions needed to interpret the side-view diagram. -/
inductive SpatialDirection where
  | right
  | upward
  | downward
  | upAndRight
  deriving DecidableEq, Repr

/-- Rendering style of the pictured electron trajectory. -/
inductive TrajectoryStyle where
  | dashedParabolicArc
  | other
  deriving DecidableEq, Repr

/-- Idealization used while the electron is between the plates. -/
inductive ElectronMotionModel where
  | uniformElectricFieldOnlyNoGravityOrDrag
  | other
  deriving DecidableEq, Repr

/-!
Typed content read from the supplied raster.  The horizontal range label is a
physical length; its numerical centimetre readout is stated separately.
-/
structure ParallelPlateFigure where
  showsPlate : PlateLabel → Bool
  platePolarity : PlateLabel → PlatePolarity
  plateArrangement : PlateArrangement
  launchPlate : PlateLabel
  landingPlate : PlateLabel
  initialVelocityArrowLabel : String
  initialVelocityArrowDirection : SpatialDirection
  launchAngleLabelDegrees : ℝ
  horizontalRangeLabel : LengthQuantity
  showsTrajectory : Bool
  trajectoryStyle : TrajectoryStyle

/-!
The independent physical objects and observables.  In particular, neither
`electricFieldStrength` nor `accelerationMagnitude` is defined from the
recorded answer or from the desired `3.6 * 10^3 N/C` value.
-/
structure CapacitorElectronSetup where
  particleSpecies : ParticleSpecies
  particleChargeSign : ChargeSign
  particleChargeMagnitude : ChargeMagnitudeQuantity
  particleMass : MassQuantity
  initialSpeed : SpeedQuantity
  launchAngleRadians : ℝ
  horizontalRange : LengthQuantity
  plateSeparation : LengthQuantity
  flightDuration : TimeQuantity
  accelerationMagnitude : AccelerationQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 3
  capacitorInterior : Set (Time × Space 3)
  electricFieldDirection : SpatialDirection
  electricForceDirection : SpatialDirection
  accelerationDirection : SpatialDirection
  motionModel : ElectronMotionModel
  figure : ParallelPlateFigure

/-! ## Assumptions: source readouts, reference data, and governing laws -/

/-!
Problem-statement and primary-image evidence.  The raster shows negative marks
on the upper plate and positive marks on the lower plate, even though the
auxiliary caption says that the upper plate is unmarked.  No field-strength
answer occurs in these data.
-/
structure MatchesProblemAndFigureReadouts
    (setup : CapacitorElectronSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  electronChargeIsNegative : setup.particleChargeSign = .negative
  speedMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 5 * 10 ^ 6
  launchAngleIsFortyFiveDegrees :
    setup.launchAngleRadians = Real.pi / 4
  rangeCentimeters :
    lengthInCentimeters setup.horizontalRange = 4
  rangeMeters :
    lengthInMeters setup.horizontalRange = 4 / 100
  bothPlatesShown :
    setup.figure.showsPlate .upper = true ∧
      setup.figure.showsPlate .lower = true
  platesAreParallel : setup.figure.plateArrangement = .parallel
  upperPlateIsNegative :
    setup.figure.platePolarity .upper = .negative
  lowerPlateIsPositive :
    setup.figure.platePolarity .lower = .positive
  launchedFromPositiveLowerPlate : setup.figure.launchPlate = .lower
  landsOnLowerPlate : setup.figure.landingPlate = .lower
  velocityArrowIsVZero : setup.figure.initialVelocityArrowLabel = "v₀"
  velocityArrowPointsUpAndRight :
    setup.figure.initialVelocityArrowDirection = .upAndRight
  angleLabelDegrees : setup.figure.launchAngleLabelDegrees = 45
  rangeLabelIsPhysicalRange :
    setup.figure.horizontalRangeLabel = setup.horizontalRange
  figureShowsDashedTrajectory : setup.figure.showsTrajectory = true
  trajectoryIsDashedParabolicArc :
    setup.figure.trajectoryStyle = .dashedParabolicArc

/-!
Standard reference calibrations needed to turn the electron's acceleration
into an electric-field strength.  These are independent particle data, not a
statement of the requested field value.
-/
structure UsesElectronReferenceConstants
    (setup : CapacitorElectronSetup) : Prop where
  massCalibration :
    massInKilograms setup.particleMass = electronRestMassInKilograms
  chargeMagnitudeCalibration :
    chargeInCoulombs setup.particleChargeMagnitude =
      elementaryChargeInCoulombs

/-- Positivity and non-vacuity conditions for the physical experiment. -/
structure HasPhysicalParameters (setup : CapacitorElectronSetup) : Prop where
  massPositive : 0 < massInKilograms setup.particleMass
  chargeMagnitudePositive :
    0 < chargeInCoulombs setup.particleChargeMagnitude
  initialSpeedPositive : 0 < speedInMetersPerSecond setup.initialSpeed
  rangePositive : 0 < lengthInMeters setup.horizontalRange
  plateSeparationPositive : 0 < lengthInMeters setup.plateSeparation
  flightDurationPositive : 0 < timeInSeconds setup.flightDuration
  accelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.accelerationMagnitude
  electricFieldStrengthPositive :
    0 < electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  capacitorInteriorNonempty : setup.capacitorInterior.Nonempty

/-!
Uniform parallel-plate electrostatics: the field points from the positive
lower plate toward the negative upper plate, and its scalar physical strength
is the norm of Physlib's spacetime-dependent vector field throughout the gap.
This law contains no numerical value for the field strength.
-/
structure SatisfiesUniformParallelPlateFieldModel
    (setup : CapacitorElectronSetup) : Prop where
  fieldPointsUpward : setup.electricFieldDirection = .upward
  electricForcePointsDownward : setup.electricForceDirection = .downward
  accelerationPointsDownward : setup.accelerationDirection = .downward
  uniformMagnitude :
    ∀ time position, (time, position) ∈ setup.capacitorInterior →
      ‖setup.electricField time position‖ =
        electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength

/-!
Equal-height constant-acceleration endpoint equations.  Horizontally the
electron moves uniformly; vertically its initial upward component is exactly
cancelled by the downward electric acceleration at landing.  These are the
general kinematic laws, not the requested electric-field result.
-/
structure SatisfiesConstantElectricAccelerationKinematics
    (setup : CapacitorElectronSetup) : Prop where
  idealMotionModel :
    setup.motionModel = .uniformElectricFieldOnlyNoGravityOrDrag
  horizontalEndpoint :
    lengthInMeters setup.horizontalRange =
      speedInMetersPerSecond setup.initialSpeed *
        Real.cos setup.launchAngleRadians *
          timeInSeconds setup.flightDuration
  verticalEndpoint :
    speedInMetersPerSecond setup.initialSpeed *
          Real.sin setup.launchAngleRadians *
          timeInSeconds setup.flightDuration =
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
          timeInSeconds setup.flightDuration ^ 2

/-!
The magnitude form of the electric part of the Lorentz-force law together
with Newton's second law: `m a = |q| E`.  Directional information for the
negative electron is kept in the parallel-plate field model above.
-/
structure SatisfiesElectricForceLaw
    (setup : CapacitorElectronSetup) : Prop where
  forceMagnitude :
    massInKilograms setup.particleMass *
        accelerationInMetersPerSecondSquared setup.accelerationMagnitude =
      chargeInCoulombs setup.particleChargeMagnitude *
        electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength

/-! ## Derived relation and displayed answer -/

/-!
At `45°`, the equal-height endpoint equations give `a = v₀² / R`; combining
this with `m a = |q| E` gives the exact SI-readout relation below.  The field
strength remains an independent physical observable in the setup.
-/
lemma electricFieldStrength_eq_mass_mul_speed_sq_div_charge_mul_range
    (setup : CapacitorElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hKinematics : SatisfiesConstantElectricAccelerationKinematics setup)
    (hForce : SatisfiesElectricForceLaw setup) :
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength =
      massInKilograms setup.particleMass *
        speedInMetersPerSecond setup.initialSpeed ^ 2 /
          (chargeInCoulombs setup.particleChargeMagnitude *
            lengthInMeters setup.horizontalRange) := by
  have hCosSq : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hHorizontalSq :
      lengthInMeters setup.horizontalRange ^ 2 =
        (1 / 2 : ℝ) *
          speedInMetersPerSecond setup.initialSpeed ^ 2 *
            timeInSeconds setup.flightDuration ^ 2 := by
    calc
      lengthInMeters setup.horizontalRange ^ 2 =
          (speedInMetersPerSecond setup.initialSpeed *
              Real.cos setup.launchAngleRadians *
                timeInSeconds setup.flightDuration) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hKinematics.horizontalEndpoint
      _ = (1 / 2 : ℝ) *
            speedInMetersPerSecond setup.initialSpeed ^ 2 *
              timeInSeconds setup.flightDuration ^ 2 := by
        rw [hData.launchAngleIsFortyFiveDegrees, Real.cos_pi_div_four]
        simp only [mul_pow, hCosSq]
        ring
  have hVerticalRange :
      lengthInMeters setup.horizontalRange =
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
            timeInSeconds setup.flightDuration ^ 2 := by
    calc
      lengthInMeters setup.horizontalRange =
          speedInMetersPerSecond setup.initialSpeed *
              Real.cos setup.launchAngleRadians *
                timeInSeconds setup.flightDuration :=
        hKinematics.horizontalEndpoint
      _ = speedInMetersPerSecond setup.initialSpeed *
              Real.sin setup.launchAngleRadians *
                timeInSeconds setup.flightDuration := by
        rw [hData.launchAngleIsFortyFiveDegrees, Real.cos_pi_div_four,
          Real.sin_pi_div_four]
      _ = (1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
              timeInSeconds setup.flightDuration ^ 2 :=
        hKinematics.verticalEndpoint
  have hTimeFactorNe :
      (1 / 2 : ℝ) * timeInSeconds setup.flightDuration ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (ne_of_gt hPhysical.flightDurationPositive))
  have hVerticalMul := congrArg
    (fun x : ℝ => x * lengthInMeters setup.horizontalRange) hVerticalRange
  have hCancel :
      ((1 / 2 : ℝ) * timeInSeconds setup.flightDuration ^ 2) *
          speedInMetersPerSecond setup.initialSpeed ^ 2 =
        ((1 / 2 : ℝ) * timeInSeconds setup.flightDuration ^ 2) *
          (accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
            lengthInMeters setup.horizontalRange) := by
    calc
      ((1 / 2 : ℝ) * timeInSeconds setup.flightDuration ^ 2) *
          speedInMetersPerSecond setup.initialSpeed ^ 2 =
          (1 / 2 : ℝ) *
            speedInMetersPerSecond setup.initialSpeed ^ 2 *
              timeInSeconds setup.flightDuration ^ 2 := by ring
      _ = lengthInMeters setup.horizontalRange ^ 2 :=
        hHorizontalSq.symm
      _ = ((1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
              timeInSeconds setup.flightDuration ^ 2) *
            lengthInMeters setup.horizontalRange := by
        simpa [pow_two] using hVerticalMul
      _ = ((1 / 2 : ℝ) * timeInSeconds setup.flightDuration ^ 2) *
          (accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
            lengthInMeters setup.horizontalRange) := by ring
  have hAccelerationRange :
      accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
          lengthInMeters setup.horizontalRange =
        speedInMetersPerSecond setup.initialSpeed ^ 2 :=
    (mul_left_cancel₀ hTimeFactorNe hCancel).symm
  have hDenominatorNe :
      chargeInCoulombs setup.particleChargeMagnitude *
          lengthInMeters setup.horizontalRange ≠ 0 :=
    mul_ne_zero (ne_of_gt hPhysical.chargeMagnitudePositive)
      (ne_of_gt hPhysical.rangePositive)
  apply (eq_div_iff hDenominatorNe).2
  calc
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength *
        (chargeInCoulombs setup.particleChargeMagnitude *
          lengthInMeters setup.horizontalRange) =
        (chargeInCoulombs setup.particleChargeMagnitude *
          electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength) *
            lengthInMeters setup.horizontalRange := by ring
    _ = (massInKilograms setup.particleMass *
          accelerationInMetersPerSecondSquared setup.accelerationMagnitude) *
            lengthInMeters setup.horizontalRange := by
      rw [hForce.forceMagnitude]
    _ = massInKilograms setup.particleMass *
          (accelerationInMetersPerSecondSquared setup.accelerationMagnitude *
            lengthInMeters setup.horizontalRange) := by ring
    _ = massInKilograms setup.particleMass *
          speedInMetersPerSecond setup.initialSpeed ^ 2 := by
      rw [hAccelerationRange]

/-- Labels of the four field-strength choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Electric-field strength in newtons/coulomb printed beside each choice. -/
def answerStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => (13 / 10 : ℝ) * 10 ^ 5
  | .B => (53 / 10 : ℝ) * 10 ^ 4
  | .C => (10 / 10 : ℝ) * 10 ^ 5
  | .D => (36 / 10 : ℝ) * 10 ^ 3

/-!
Half of one unit in the last displayed significant digit.  This gives a
precise meaning to matching the rounded numerical choices.
-/
def answerRoundingTolerance : AnswerChoice → ℝ
  | .A => 5 * 10 ^ 3
  | .B => 5 * 10 ^ 2
  | .C => 5 * 10 ^ 3
  | .D => 5 * 10 ^ 1

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice matches the independently modeled physical field when the SI
readout lies within half a unit of the choice's last displayed digit.
-/
def AnswerMatchesElectricField
    (setup : CapacitorElectronSetup) (choice : AnswerChoice) : Prop :=
  |electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength -
      answerStrengthInNewtonsPerCoulomb choice| ≤
    answerRoundingTolerance choice

/-!
The launch data, CODATA electron constants, ideal endpoint kinematics, and
electric-force law put the field within `50 N/C` of `3.6 * 10^3 N/C`, so the
two-significant-digit displayed answer is choice D.
-/
lemma electricFieldStrength_rounds_to_threePointSixTimesTenCubed
    (setup : CapacitorElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hConstants : UsesElectronReferenceConstants setup)
    (hPhysical : HasPhysicalParameters setup)
    (hKinematics : SatisfiesConstantElectricAccelerationKinematics setup)
    (hForce : SatisfiesElectricForceLaw setup) :
    |electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength -
        (36 / 10 : ℝ) * 10 ^ 3| ≤ 50 := by
  rw [electricFieldStrength_eq_mass_mul_speed_sq_div_charge_mul_range
    setup hData hPhysical hKinematics hForce]
  rw [hConstants.massCalibration, hConstants.chargeMagnitudeCalibration,
    hData.speedMetersPerSecond, hData.rangeMeters]
  have hElementary :
      elementaryChargeInCoulombs = (1.602176634e-19 : ℝ) := by
    simp only [elementaryChargeInCoulombs, ChargeUnit.elementaryCharge,
      ChargeUnit.scale_div_self]
    rfl
  rw [hElementary]
  unfold electronRestMassInKilograms
  norm_num [abs_le]

/-!
The electron's parabolic return over `4.0 cm` requires an electric-field
strength that rounds to `3.6 * 10^3 N/C`, the value printed as choice D.

This declaration formalizes `thm:physics:phyx_mini_0836:target`.  Neither the
rounded value, its tolerance statement, nor the matching answer occurs in any
premise or governing-law structure.
-/
theorem problem_phyx_mini_0836
    (setup : CapacitorElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hConstants : UsesElectronReferenceConstants setup)
    (hPhysical : HasPhysicalParameters setup)
    (hFieldModel : SatisfiesUniformParallelPlateFieldModel setup)
    (hKinematics : SatisfiesConstantElectricAccelerationKinematics setup)
    (hForce : SatisfiesElectricForceLaw setup) :
    |electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength -
        (36 / 10 : ℝ) * 10 ^ 3| ≤ 50 ∧
      AnswerMatchesElectricField setup recordedDatasetAnswer := by
  have hRound :=
    electricFieldStrength_rounds_to_threePointSixTimesTenCubed
      setup hData hConstants hPhysical hKinematics hForce
  constructor
  · exact hRound
  · norm_num [AnswerMatchesElectricField, recordedDatasetAnswer,
      answerStrengthInNewtonsPerCoulomb, answerRoundingTolerance] at hRound ⊢
    exact hRound

end PhyXMiniProblems.ProblemPhyXMini0836
