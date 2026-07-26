import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0687

open Dimension

/-!
# Rotation rate of the Ames 20-g centrifuge

The centrifuge is modeled as a horizontal `58 ft` tube rotating about a
vertical shaft through its midpoint.  The astronaut is seated at the right
end, facing the shaft, at the `29 ft` radius printed in the supplied image.
The requested physical rotation frequency is constrained by the standard
relations

`omega = 2 * pi * f` and `a_c = omega^2 * r`.

Lengths, accelerations, angular speed, and rotation frequency are represented
by unit-independent Physlib quantities.  Real numbers occur only as named
readouts, dimensionless revolution counts, the stated multiple of standard
gravity, and the displayed answer-choice values.

Assumption/target split:

* governing laws: the `20 g` acceleration specification, the conversion from
  rotation frequency to angular speed, and uniform circular kinematics;
* previous-part results: none;
* data and figure readouts: the `58 ft` full tube, the `29 ft` center-to-seat
  distance, the printed `29 ft` image label, the astronaut's orientation, and
  a standard-gravity calibration of `9.8 m/s^2`;
* target conclusions: proximity to `0.75 rev/s` and `45 rev/min`, and the
  unique selection of answer choice C.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of acceleration, `length / time^2`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of both angular speed and rotation frequency. -/
def inverseTimeDimension : Dimension := T𝓭⁻¹

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude, with radians dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim inverseTimeDimension NNReal)

/-- A nonnegative rotation frequency, with revolutions dimensionless. -/
abbrev RotationFrequencyQuantity : Type :=
  Dimensionful (WithDim inverseTimeDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an acceleration in coherent units induced by length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a rotation frequency in revolutions per selected time unit. -/
def rotationFrequencyReadout
    (timeUnit : TimeUnit) (frequency : RotationFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Foot readout used for the two stated apparatus lengths. -/
def lengthInFeet (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.feet length

/-- Coherent SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Coherent SI metre-per-second-squared acceleration readout. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds angularSpeed

/-- Rotation frequency in revolutions per second. -/
def rotationFrequencyInRevolutionsPerSecond
    (frequency : RotationFrequencyQuantity) : ℝ :=
  rotationFrequencyReadout TimeUnit.seconds frequency

/-- Rotation frequency in revolutions per minute. -/
def rotationFrequencyInRevolutionsPerMinute
    (frequency : RotationFrequencyQuantity) : ℝ :=
  rotationFrequencyReadout TimeUnit.minutes frequency

/-!
General unit-conversion facts.  Neither lemma mentions this centrifuge's
unknown rotation rate or any answer choice.
-/

/-- One foot is exactly `0.3048 m = 381/1250 m`. -/
lemma lengthInMeters_eq_feet_mul_conversion
    (length : LengthQuantity) :
    lengthInMeters length = (381 / 1250 : ℝ) * lengthInFeet length := by
  let uFeet : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.feet }
  let uMeters : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.meters }
  have h := congrArg
    (fun quantity : WithDim L𝓭 NNReal => (quantity.val : ℝ))
    (length.2 uFeet uMeters)
  norm_num [lengthInMeters, lengthInFeet, lengthReadout, uFeet, uMeters,
    UnitChoices.dimScale, LengthUnit.feet, LengthUnit.scale,
    LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
  exact h

/-- A per-minute frequency readout is sixty times its per-second readout. -/
lemma rotationFrequency_perMinute_eq_sixty_mul_perSecond
    (frequency : RotationFrequencyQuantity) :
    rotationFrequencyInRevolutionsPerMinute frequency =
      60 * rotationFrequencyInRevolutionsPerSecond frequency := by
  let uSeconds : UnitChoices :=
    { UnitChoices.SI with time := TimeUnit.seconds }
  let uMinutes : UnitChoices :=
    { UnitChoices.SI with time := TimeUnit.minutes }
  have hscale :
      uSeconds.dimScale uMinutes inverseTimeDimension = 60 := by
    unfold inverseTimeDimension
    rw [UnitChoices.dimScale_of_inv_eq_swap]
    norm_num [uSeconds, uMinutes, UnitChoices.dimScale,
      TimeUnit.minutes, TimeUnit.scale, TimeUnit.seconds,
      TimeUnit.div_eq_val]
    apply NNReal.eq
    rfl
  have hUnits := frequency.2 uSeconds uMinutes
  rw [show dim (WithDim inverseTimeDimension NNReal) =
    inverseTimeDimension by rfl, hscale] at hUnits
  have h := congrArg
    (fun quantity : WithDim inverseTimeDimension NNReal =>
      (quantity.val : ℝ)) hUnits
  norm_num [WithDim.smul_val, NNReal.smul_def] at h
  simpa [rotationFrequencyInRevolutionsPerMinute,
    rotationFrequencyInRevolutionsPerSecond, rotationFrequencyReadout,
    uSeconds, uMinutes] using h

/-! ## Apparatus roles and primary-image vocabulary -/

/-- Orientation of the long centrifuge tube. -/
inductive TubeOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Location of the rotation axis relative to the full tube. -/
inductive RotationAxisLocation where
  | verticalThroughTubeMidpoint
  | other
  deriving DecidableEq, Repr

/-- Direction in which the seated astronaut faces. -/
inductive AstronautOrientation where
  | facingRotationAxis
  | facingAwayFromRotationAxis
  deriving DecidableEq, Repr

/-- Distinct objects visibly present in the supplied centrifuge image. -/
inductive FigureObject where
  | horizontalTrussBeam
  | centralVerticalShaft
  | leftRedClamp
  | rightRedClamp
  | astronautSeat
  | seatedAstronaut
  deriving DecidableEq, Fintype, Repr

/-- The sole numerical distance label visible in the supplied image. -/
inductive FigureTextLabel where
  | radiusTwentyNineFeet
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from image `687.png`.  The dimension line
runs from the central shaft to the right end containing the astronaut.
-/
structure AmesCentrifugeFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  printedText : FigureTextLabel → String
  dimensionStartsAtCentralAxis : Bool
  dimensionEndsAtRightTubeEnd : Bool
  astronautShownAtRightEnd : Bool
  astronautShownFacingCentralAxis : Bool
  shaftShownAtBeamMidpoint : Bool

/-! ## Independent physical setup -/

/-!
The requested rotation frequency and its angular speed are independent
physical fields.  They are related to the supplied geometry and acceleration
only through the governing-law structures below; neither is defined using a
numerical answer.
-/
structure AmesTwentyGCentrifugeSetup where
  fullTubeLength : LengthQuantity
  astronautRadius : LengthQuantity
  standardGravity : AccelerationQuantity
  requiredCentripetalAcceleration : AccelerationQuantity
  rotationFrequency : RotationFrequencyQuantity
  angularSpeed : AngularSpeedQuantity
  statedAccelerationInG : ℝ
  tubeOrientation : TubeOrientation
  rotationAxisLocation : RotationAxisLocation
  astronautOrientation : AstronautOrientation
  tubeIsCylindrical : Bool
  astronautSeatedAtTubeEnd : Bool
  rotationIsSteady : Bool
  figure : AmesCentrifugeFigure

/-! ## Scenario, source data, and figure readouts -/

/-- Qualitative physical scenario stated in the problem prose. -/
structure MatchesAmesCentrifugeScenario
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  tubeIsHorizontal : setup.tubeOrientation = .horizontal
  tubeIsCylindrical : setup.tubeIsCylindrical = true
  axisPassesThroughMidpoint :
    setup.rotationAxisLocation = .verticalThroughTubeMidpoint
  astronautSitsAtOneEnd : setup.astronautSeatedAtTubeEnd = true
  astronautFacesAxis : setup.astronautOrientation = .facingRotationAxis
  steadyRotation : setup.rotationIsSteady = true

/-!
Numerical quantities supplied by the problem.  No rotation frequency or
answer-choice value occurs in this structure.
-/
structure MatchesCentrifugeProblemReadouts
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  fullTubeLengthFeet : lengthInFeet setup.fullTubeLength = 58
  astronautRadiusFeet : lengthInFeet setup.astronautRadius = 29
  requestedAccelerationMultiple : setup.statedAccelerationInG = 20

/-- Direct evidence from the primary bitmap and its printed dimension line. -/
structure MatchesPrimaryCentrifugeFigure
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  everyDepictedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  radiusLabelShown :
    setup.figure.showsTextLabel .radiusTwentyNineFeet = true
  radiusLabelText :
    setup.figure.printedText .radiusTwentyNineFeet = "29 ft"
  dimensionLineStartsAtAxis :
    setup.figure.dimensionStartsAtCentralAxis = true
  dimensionLineEndsAtRightEnd :
    setup.figure.dimensionEndsAtRightTubeEnd = true
  astronautAtRightEnd : setup.figure.astronautShownAtRightEnd = true
  astronautFacesCenter :
    setup.figure.astronautShownFacingCentralAxis = true
  centralShaftAtMidpoint : setup.figure.shaftShownAtBeamMidpoint = true
  radiusIsHalfFullLength : ∀ unit : LengthUnit,
    2 * lengthReadout unit setup.astronautRadius =
      lengthReadout unit setup.fullTubeLength

/-!
Rounded standard gravitational acceleration used for the classroom
calculation.  It calibrates `g`; it does not constrain the rotation rate.
-/
structure UsesRoundedStandardGravity
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.standardGravity = 49 / 5

/-! ## Governing physics -/

/-- Positivity assumptions selecting the nondegenerate physical branch. -/
structure HasPhysicalCentrifugeParameters
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  positiveTubeLength : 0 < lengthInMeters setup.fullTubeLength
  positiveAstronautRadius : 0 < lengthInMeters setup.astronautRadius
  positiveStandardGravity :
    0 < accelerationInMetersPerSecondSquared setup.standardGravity
  positiveRequiredAcceleration :
    0 < accelerationInMetersPerSecondSquared
      setup.requiredCentripetalAcceleration
  positiveRotationFrequency :
    0 < rotationFrequencyInRevolutionsPerSecond setup.rotationFrequency
  positiveAngularSpeed :
    0 < angularSpeedInRadiansPerSecond setup.angularSpeed

/-!
The requested centripetal acceleration is the stated dimensionless multiple
of local standard gravity.  This is the meaning of `20 g`, not an assumption
about the requested rotation rate.
-/
structure SatisfiesStatedGLevel
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  requiredAccelerationIsStatedMultipleOfGravity :
    accelerationInMetersPerSecondSquared
        setup.requiredCentripetalAcceleration =
      setup.statedAccelerationInG *
        accelerationInMetersPerSecondSquared setup.standardGravity

/-!
Uniform circular-motion laws in coherent SI readouts.  Radians and
revolutions are dimensionless, with one revolution corresponding to `2*pi`
radians.
-/
structure SatisfiesUniformCircularMotion
    (setup : AmesTwentyGCentrifugeSetup) : Prop where
  angularSpeedFromRotationFrequency :
    angularSpeedInRadiansPerSecond setup.angularSpeed =
      2 * Real.pi *
        rotationFrequencyInRevolutionsPerSecond setup.rotationFrequency
  centripetalAccelerationLaw :
    accelerationInMetersPerSecondSquared
        setup.requiredCentripetalAcceleration =
      angularSpeedInRadiansPerSecond setup.angularSpeed ^ 2 *
        lengthInMeters setup.astronautRadius

/-!
An algebraic consequence of the two circular-motion laws.  This leaves the
positive square-root selection and all numerical evaluation to later proofs.
-/
lemma rotationFrequency_sq_eq_acceleration_div_radius_and_four_pi_sq
    (setup : AmesTwentyGCentrifugeSetup)
    (h_physical : HasPhysicalCentrifugeParameters setup)
    (h_motion : SatisfiesUniformCircularMotion setup) :
    rotationFrequencyInRevolutionsPerSecond setup.rotationFrequency ^ 2 =
      accelerationInMetersPerSecondSquared
          setup.requiredCentripetalAcceleration /
        ((2 * Real.pi) ^ 2 * lengthInMeters setup.astronautRadius) := by
  rw [h_motion.centripetalAccelerationLaw,
    h_motion.angularSpeedFromRotationFrequency]
  field_simp [ne_of_gt h_physical.positiveAstronautRadius, Real.pi_ne_zero]

/-! ## Displayed choices and formalization target -/

/-- Labels of the four rotation-rate choices printed by the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Revolution-per-minute value displayed beside each answer label. -/
def AnswerChoice.rateRevolutionsPerMinute : AnswerChoice → ℝ
  | .A => 643 / 10
  | .B => 45 / 2
  | .C => 45
  | .D => 36

/-!
The required frequency is approximately `0.75 rev/s`, equivalently
`45 rev/min`.  The tolerances express the rounding inherent in using
`g = 9.8 m/s^2`, the three-significant-figure radius, and displayed decimal
answer choices.  The final conjunct states that C is the unique nearest
displayed choice.
-/
theorem required_rotation_rate_is_choice_C
    (setup : AmesTwentyGCentrifugeSetup)
    (h_scenario : MatchesAmesCentrifugeScenario setup)
    (h_readouts : MatchesCentrifugeProblemReadouts setup)
    (h_figure : MatchesPrimaryCentrifugeFigure setup)
    (h_gravity : UsesRoundedStandardGravity setup)
    (h_g_level : SatisfiesStatedGLevel setup)
    (h_physical : HasPhysicalCentrifugeParameters setup)
    (h_motion : SatisfiesUniformCircularMotion setup) :
    |rotationFrequencyInRevolutionsPerSecond setup.rotationFrequency -
        (3 / 4 : ℝ)| < 1 / 1000 ∧
      |rotationFrequencyInRevolutionsPerMinute setup.rotationFrequency - 45| <
        1 / 10 ∧
      ∀ choice : AnswerChoice, choice ≠ .C →
        |rotationFrequencyInRevolutionsPerMinute setup.rotationFrequency -
            AnswerChoice.rateRevolutionsPerMinute .C| <
          |rotationFrequencyInRevolutionsPerMinute setup.rotationFrequency -
            AnswerChoice.rateRevolutionsPerMinute choice| := by
  have hr :=
    lengthInMeters_eq_feet_mul_conversion setup.astronautRadius
  rw [h_readouts.astronautRadiusFeet] at hr
  norm_num at hr
  have ha :=
    h_g_level.requiredAccelerationIsStatedMultipleOfGravity
  rw [h_readouts.requestedAccelerationMultiple,
    h_gravity.gravityMetersPerSecondSquared] at ha
  norm_num at ha
  have hsq :=
    rotationFrequency_sq_eq_acceleration_div_radius_and_four_pi_sq
      setup h_physical h_motion
  rw [ha, hr] at hsq
  field_simp [Real.pi_ne_zero] at hsq
  ring_nf at hsq
  let f :=
    rotationFrequencyInRevolutionsPerSecond setup.rotationFrequency
  change f ^ 2 * Real.pi ^ 2 * 44196 = 245000 at hsq
  have hf_pos : 0 < f :=
    h_physical.positiveRotationFrequency
  have hx_sq :
      (Real.pi * f) ^ 2 = (245000 / 44196 : ℝ) := by
    rw [mul_pow]
    nlinarith [hsq]
  have hpi_upper : Real.pi < (31416 / 10000 : ℝ) := by
    convert Real.pi_lt_d4 using 1
    norm_num
  have hpi_lower : (31415 / 10000 : ℝ) < Real.pi := by
    convert Real.pi_gt_d4 using 1
    norm_num
  have hx_pos : 0 < Real.pi * f :=
    mul_pos Real.pi_pos hf_pos
  have hf_lower : (749 / 1000 : ℝ) < f := by
    by_contra h
    have hf_le : f ≤ (749 / 1000 : ℝ) :=
      le_of_not_gt h
    have hprod :
        Real.pi * f <
          (31416 / 10000 : ℝ) * (749 / 1000 : ℝ) := calc
      Real.pi * f < (31416 / 10000 : ℝ) * f :=
        mul_lt_mul_of_pos_right hpi_upper hf_pos
      _ ≤ (31416 / 10000 : ℝ) * (749 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_left hf_le (by norm_num)
    have hsq_lt :=
      (sq_lt_sq₀ hx_pos.le (by norm_num)).2 hprod
    rw [hx_sq] at hsq_lt
    norm_num at hsq_lt
  have hf_upper : f < (751 / 1000 : ℝ) := by
    by_contra h
    have hf_ge : (751 / 1000 : ℝ) ≤ f :=
      le_of_not_gt h
    have hprod :
        (31415 / 10000 : ℝ) * (751 / 1000 : ℝ) <
          Real.pi * f := calc
      (31415 / 10000 : ℝ) * (751 / 1000 : ℝ) ≤
          (31415 / 10000 : ℝ) * f :=
        mul_le_mul_of_nonneg_left hf_ge (by norm_num)
      _ < Real.pi * f :=
        mul_lt_mul_of_pos_right hpi_lower hf_pos
    have hsq_lt :=
      (sq_lt_sq₀ (by norm_num) hx_pos.le).2 hprod
    rw [hx_sq] at hsq_lt
    norm_num at hsq_lt
  have hf_close :
      |f - (3 / 4 : ℝ)| < 1 / 1000 := by
    rw [abs_lt]
    constructor
    · nlinarith [hf_lower, hf_upper]
    · nlinarith [hf_lower, hf_upper]
  have hminute :=
    rotationFrequency_perMinute_eq_sixty_mul_perSecond
      setup.rotationFrequency
  let m :=
    rotationFrequencyInRevolutionsPerMinute setup.rotationFrequency
  change m = 60 * f at hminute
  have hm_lower : (4494 / 100 : ℝ) < m := by
    nlinarith [hminute, hf_lower]
  have hm_upper : m < (4506 / 100 : ℝ) := by
    nlinarith [hminute, hf_upper]
  have hm_close : |m - 45| < (1 / 10 : ℝ) := by
    rw [abs_lt]
    constructor
    · nlinarith [hm_lower, hm_upper]
    · nlinarith [hm_lower, hm_upper]
  refine ⟨?_, ?_, ?_⟩
  · simpa [f] using hf_close
  · simpa [m] using hm_close
  · intro choice hchoice
    change |m - AnswerChoice.rateRevolutionsPerMinute .C| <
      |m - AnswerChoice.rateRevolutionsPerMinute choice|
    cases choice with
    | A =>
        norm_num [AnswerChoice.rateRevolutionsPerMinute]
        rw [abs_of_neg
          (by nlinarith [hm_upper] : m - 643 / 10 < 0)]
        nlinarith [hm_close]
    | B =>
        norm_num [AnswerChoice.rateRevolutionsPerMinute]
        rw [abs_of_pos
          (by nlinarith [hm_lower] : 0 < m - 45 / 2)]
        nlinarith [hm_close]
    | C => exact (hchoice rfl).elim
    | D =>
        norm_num [AnswerChoice.rateRevolutionsPerMinute]
        rw [abs_of_pos
          (by nlinarith [hm_lower] : 0 < m - 36)]
        nlinarith [hm_close]

end PhyXMiniProblems.ProblemPhyXMini0687
