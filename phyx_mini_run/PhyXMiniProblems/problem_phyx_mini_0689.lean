import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0689

open Dimension

/-!
# Launch speed for a basketball shot

A basketball is released `2.00 m` above the floor at an angle of `40.0°`.
The hoop is `10.0 m` horizontally from the release point and `3.05 m` above
the floor.  The idealized flight is uniform horizontally and has constant
downward gravitational acceleration vertically.

Lengths, elapsed time, speed, and acceleration are unit-independent Physlib
quantities.  Real numbers occur only as explicitly named SI readouts,
dimensionless angle readouts, schematic figure coordinates, and displayed
multiple-choice values.

Assumption/target split:

* governing laws: uniform horizontal motion and constant-gravity vertical
  motion, together with arrival at the hoop on the descending branch;
* previous-part results: none;
* figure/data readouts: `10.0 m`, `2.00 m`, `3.05 m`, `40.0°`, standard
  near-Earth gravity, and the labelled front-of-backboard geometry;
* target conclusions: the exact launch-speed formula, the interval that
  rounds to `10.7 m/s`, and selection of displayed choice C.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `length * time⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def quantitySIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantitySIReadout length

/-- Second readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  quantitySIReadout time

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantitySIReadout acceleration

/-- Principal radian readout of a physical angle. -/
def angleInRadians (angle : Real.Angle) : ℝ :=
  angle.toReal

/-- Convert a degree readout into a physical angle. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Primary-figure vocabulary and physical setup -/

/-- Named physical locations visible in the supplied basketball diagram. -/
inductive FigureLocation where
  | releasePoint
  | hoop
  | backboard
  deriving DecidableEq, Repr

/-- Labels whose numerical values are printed in the supplied diagram. -/
inductive FigureMeasurementLabel where
  | releaseHeightTwoMeters
  | launchAngleFortyDegrees
  | horizontalDistanceTenMeters
  | hoopHeightThreePointZeroFiveMeters
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and schematic information transcribed from image `689.png`. -/
structure BasketballShotFigure where
  horizontalCoordinate : FigureLocation → ℝ
  verticalCoordinate : FigureLocation → ℝ
  measurementLabelShown : FigureMeasurementLabel → Bool
  playerShownAtReleasePoint : Bool
  hoopShownInFrontOfBackboard : Bool
  dottedArcStartsAtRelease : Bool
  dottedArcEndsAtHoop : Bool
  dottedArcHasInteriorApex : Bool

/-!
Independent physical quantities for the shot.  The launch speed is stored as
a genuine dimensionful observable, not defined from an answer choice.  The
elapsed time is the physical time at which the center of the ball reaches the
hoop plane.
-/
structure BasketballShotSetup where
  horizontalDistanceToHoop : LengthQuantity
  releaseHeight : LengthQuantity
  hoopHeight : LengthQuantity
  launchAngle : Real.Angle
  launchSpeed : DimSpeed
  gravityMagnitude : AccelerationQuantity
  timeToHoop : TimeQuantity
  figure : BasketballShotFigure

/-! ## Problem data, figure evidence, and admissibility -/

/-- Numerical quantities stated in the prose and printed on the figure. -/
structure MatchesProblemReadouts (setup : BasketballShotSetup) : Prop where
  horizontalDistanceMeters :
    lengthInMeters setup.horizontalDistanceToHoop = 10
  releaseHeightMeters : lengthInMeters setup.releaseHeight = 2
  hoopHeightMeters : lengthInMeters setup.hoopHeight = 305 / 100
  launchAngleDegrees : setup.launchAngle = degrees 40

/-- Standard near-Earth gravitational acceleration used by the answer key. -/
def UsesStandardNearEarthGravity (setup : BasketballShotSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravityMagnitude = 98 / 10

/-!
Primary-image evidence.  The schematic coordinates record only ordering and
incidence information; they are not metre readouts and do not define the
unknown launch speed.
-/
structure MatchesPrimaryBasketballFigure
    (setup : BasketballShotSetup) : Prop where
  everyMeasurementLabelShown :
    ∀ label, setup.figure.measurementLabelShown label = true
  playerAtReleasePoint : setup.figure.playerShownAtReleasePoint = true
  releaseLeftOfHoop :
    setup.figure.horizontalCoordinate .releasePoint <
      setup.figure.horizontalCoordinate .hoop
  hoopNotAboveBackboardPlane :
    setup.figure.horizontalCoordinate .hoop ≤
      setup.figure.horizontalCoordinate .backboard
  hoopInFrontOfBackboard : setup.figure.hoopShownInFrontOfBackboard = true
  hoopAboveRelease :
    setup.figure.verticalCoordinate .releasePoint <
      setup.figure.verticalCoordinate .hoop
  trajectoryStartsAtRelease : setup.figure.dottedArcStartsAtRelease = true
  trajectoryEndsAtHoop : setup.figure.dottedArcEndsAtHoop = true
  trajectoryHasInteriorApex : setup.figure.dottedArcHasInteriorApex = true

/-- Positivity and nondegeneracy conditions for the ideal shot. -/
structure HasPhysicalShotParameters (setup : BasketballShotSetup) : Prop where
  horizontalDistancePositive :
    0 < lengthInMeters setup.horizontalDistanceToHoop
  releaseHeightNonnegative : 0 ≤ lengthInMeters setup.releaseHeight
  hoopAboveRelease :
    lengthInMeters setup.releaseHeight < lengthInMeters setup.hoopHeight
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravityMagnitude
  timeToHoopPositive : 0 < timeInSeconds setup.timeToHoop
  launchAngleAcute :
    0 < angleInRadians setup.launchAngle ∧
      angleInRadians setup.launchAngle < Real.pi / 2

/-! ## Governing projectile laws -/

/-!
The ideal point-mass projectile model evaluated at the time the ball reaches
the hoop.  The first two fields are `x = v cos(θ) t` and
`y = y₀ + v sin(θ) t - g t²/2`.  The final field expresses the descending
front-rim approach shown by the dotted arc, so the ball reaches the hoop
before the backboard rather than rising into it.

None of these laws contains `10.7`, any answer label, or the solved speed
formula.
-/
structure SatisfiesIdealProjectileMotionToHoop
    (setup : BasketballShotSetup) : Prop where
  uniformHorizontalMotion :
    lengthInMeters setup.horizontalDistanceToHoop =
      speedInMetersPerSecond setup.launchSpeed *
        Real.cos (angleInRadians setup.launchAngle) *
          timeInSeconds setup.timeToHoop
  constantGravityVerticalMotion :
    lengthInMeters setup.hoopHeight =
      lengthInMeters setup.releaseHeight +
        speedInMetersPerSecond setup.launchSpeed *
          Real.sin (angleInRadians setup.launchAngle) *
            timeInSeconds setup.timeToHoop -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared setup.gravityMagnitude *
            timeInSeconds setup.timeToHoop ^ 2
  descendingAtHoop :
    speedInMetersPerSecond setup.launchSpeed *
          Real.sin (angleInRadians setup.launchAngle) -
        accelerationInMetersPerSecondSquared setup.gravityMagnitude *
          timeInSeconds setup.timeToHoop < 0

/-!
Eliminating the time-to-hoop from the two kinematic equations yields the
usual exact launch-speed formula.  This is a derived conclusion rather than
a premise of the numerical answer theorem.
-/
lemma requiredLaunchSpeed_exactFormula
    (setup : BasketballShotSetup)
    (_physical : HasPhysicalShotParameters setup)
    (_motion : SatisfiesIdealProjectileMotionToHoop setup) :
    speedInMetersPerSecond setup.launchSpeed =
      Real.sqrt
        (accelerationInMetersPerSecondSquared setup.gravityMagnitude *
            lengthInMeters setup.horizontalDistanceToHoop ^ 2 /
          (2 * Real.cos (angleInRadians setup.launchAngle) ^ 2 *
            (lengthInMeters setup.horizontalDistanceToHoop *
                Real.tan (angleInRadians setup.launchAngle) -
              (lengthInMeters setup.hoopHeight -
                lengthInMeters setup.releaseHeight)))) := by
  have hcos :
      0 < Real.cos (angleInRadians setup.launchAngle) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, _physical.launchAngleAcute.1]
    · exact _physical.launchAngleAcute.2
  have hden :
      2 * Real.cos (angleInRadians setup.launchAngle) ^ 2 *
          (lengthInMeters setup.horizontalDistanceToHoop *
              Real.tan (angleInRadians setup.launchAngle) -
            (lengthInMeters setup.hoopHeight -
              lengthInMeters setup.releaseHeight)) =
        accelerationInMetersPerSecondSquared setup.gravityMagnitude *
          Real.cos (angleInRadians setup.launchAngle) ^ 2 *
          timeInSeconds setup.timeToHoop ^ 2 := by
    calc
      2 * Real.cos (angleInRadians setup.launchAngle) ^ 2 *
            (lengthInMeters setup.horizontalDistanceToHoop *
                Real.tan (angleInRadians setup.launchAngle) -
              (lengthInMeters setup.hoopHeight -
                lengthInMeters setup.releaseHeight)) =
          2 * Real.cos (angleInRadians setup.launchAngle) ^ 2 *
            (speedInMetersPerSecond setup.launchSpeed *
                Real.sin (angleInRadians setup.launchAngle) *
                timeInSeconds setup.timeToHoop -
              (lengthInMeters setup.hoopHeight -
                lengthInMeters setup.releaseHeight)) := by
                  rw [_motion.uniformHorizontalMotion,
                    Real.tan_eq_sin_div_cos]
                  field_simp [ne_of_gt hcos]
      _ = accelerationInMetersPerSecondSquared setup.gravityMagnitude *
            Real.cos (angleInRadians setup.launchAngle) ^ 2 *
            timeInSeconds setup.timeToHoop ^ 2 := by
              nlinarith [_motion.constantGravityVerticalMotion]
  have hradicand :
      accelerationInMetersPerSecondSquared setup.gravityMagnitude *
            lengthInMeters setup.horizontalDistanceToHoop ^ 2 /
          (2 * Real.cos (angleInRadians setup.launchAngle) ^ 2 *
            (lengthInMeters setup.horizontalDistanceToHoop *
                Real.tan (angleInRadians setup.launchAngle) -
              (lengthInMeters setup.hoopHeight -
                lengthInMeters setup.releaseHeight))) =
        speedInMetersPerSecond setup.launchSpeed ^ 2 := by
    rw [hden, _motion.uniformHorizontalMotion]
    field_simp [ne_of_gt _physical.gravityPositive,
      ne_of_gt hcos, ne_of_gt _physical.timeToHoopPositive]
  rw [hradicand, Real.sqrt_sq _physical.launchSpeedPositive.le]

/-! ## Displayed choices and formalization target -/

/-- Labels of the four speed choices printed by the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside an answer label. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 66 / 10
  | .B => 82 / 10
  | .C => 107 / 10
  | .D => 28 / 10

/-- The physical speed agrees with a displayed one-decimal-place readout. -/
def MatchesDisplayedSpeed
    (setup : BasketballShotSetup) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond setup.launchSpeed -
      choice.speedInMetersPerSecond| ≤ 1 / 20

/-- A choice is at least as close to the physical speed as every other choice. -/
def IsClosestDisplayedChoice
    (setup : BasketballShotSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    |speedInMetersPerSecond setup.launchSpeed -
        choice.speedInMetersPerSecond| ≤
      |speedInMetersPerSecond setup.launchSpeed -
        otherChoice.speedInMetersPerSecond|

/-!
For the stated geometry, angle, and standard gravity, the required speed lies
strictly between `10.65 m/s` and `10.75 m/s` and hence rounds to `10.7 m/s`.
-/
lemma requiredLaunchSpeed_bounds
    (setup : BasketballShotSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalShotParameters setup)
    (_motion : SatisfiesIdealProjectileMotionToHoop setup) :
    (213 / 20 : ℝ) < speedInMetersPerSecond setup.launchSpeed ∧
      speedInMetersPerSecond setup.launchSpeed < (215 / 20 : ℝ) := by
  have hangle :
      angleInRadians setup.launchAngle = 2 * Real.pi / 9 := by
    rw [_readouts.launchAngleDegrees]
    change ((↑((40 : ℝ) * Real.pi / 180) : Real.Angle).toReal =
      2 * Real.pi / 9)
    rw [show (40 : ℝ) * Real.pi / 180 = 2 * Real.pi / 9 by ring]
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have hcosPos : 0 < Real.cos (2 * Real.pi / 9) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsinPos : 0 < Real.sin (2 * Real.pi / 9) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hcosBounds :
      (68938 / 90000 : ℝ) < Real.cos (2 * Real.pi / 9) ∧
        Real.cos (2 * Real.pi / 9) < (68952 / 90000 : ℝ) := by
    have hCubic :
        4 * Real.cos (2 * Real.pi / 9) ^ 3 -
            3 * Real.cos (2 * Real.pi / 9) = -(1 / 2 : ℝ) := by
      have hTriple :
          Real.cos (3 * (2 * Real.pi / 9)) =
            4 * Real.cos (2 * Real.pi / 9) ^ 3 -
              3 * Real.cos (2 * Real.pi / 9) := by
        rw [show 3 * (2 * Real.pi / 9) =
          2 * (2 * Real.pi / 9) + 2 * Real.pi / 9 by ring,
          Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
        have hTrigMul := congrArg
          (fun x : ℝ => x * Real.cos (2 * Real.pi / 9))
          (Real.sin_sq_add_cos_sq (2 * Real.pi / 9))
        ring_nf at hTrigMul ⊢
        linarith
      rw [show 3 * (2 * Real.pi / 9) =
        Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hTriple
      norm_num at hTriple ⊢
      exact hTriple.symm
    have hHalf : (1 / 2 : ℝ) < Real.cos (2 * Real.pi / 9) := by
      rw [← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi
        (by positivity) (by linarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    constructor
    · by_contra h
      have hLe :
          Real.cos (2 * Real.pi / 9) ≤ (68938 / 90000 : ℝ) :=
        le_of_not_gt h
      have hBracket : 0 <
          4 * ((68938 / 90000 : ℝ) ^ 2 +
            (68938 / 90000 : ℝ) * Real.cos (2 * Real.pi / 9) +
            Real.cos (2 * Real.pi / 9) ^ 2) - 3 := by
        nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 9) - 1 / 2)]
      have hProduct : 0 ≤
          ((68938 / 90000 : ℝ) - Real.cos (2 * Real.pi / 9)) *
            (4 * ((68938 / 90000 : ℝ) ^ 2 +
              (68938 / 90000 : ℝ) * Real.cos (2 * Real.pi / 9) +
              Real.cos (2 * Real.pi / 9) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.2 hLe) hBracket.le
      nlinarith
    · by_contra h
      have hGe :
          (68952 / 90000 : ℝ) ≤ Real.cos (2 * Real.pi / 9) :=
        le_of_not_gt h
      have hBracket : 0 <
          4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
            Real.cos (2 * Real.pi / 9) * (68952 / 90000 : ℝ) +
            (68952 / 90000 : ℝ) ^ 2) - 3 := by
        nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 9) - 1 / 2)]
      have hProduct : 0 ≤
          (Real.cos (2 * Real.pi / 9) - (68952 / 90000 : ℝ)) *
            (4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
              Real.cos (2 * Real.pi / 9) * (68952 / 90000 : ℝ) +
              (68952 / 90000 : ℝ) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.2 hGe) hBracket.le
      nlinarith
  have hsinBounds :
      (6426 / 10000 : ℝ) < Real.sin (2 * Real.pi / 9) ∧
        Real.sin (2 * Real.pi / 9) < (6430 / 10000 : ℝ) := by
    have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi / 9)
    constructor
    · have hcSquareUpper : Real.cos (2 * Real.pi / 9) ^ 2 <
          (68952 / 90000 : ℝ) ^ 2 := by
        nlinarith [mul_pos
          (sub_pos.mpr hcosBounds.2)
          (add_pos hcosPos (by norm_num : (0 : ℝ) < 68952 / 90000))]
      by_contra h
      have hsLe :
          Real.sin (2 * Real.pi / 9) ≤ (6426 / 10000 : ℝ) :=
        le_of_not_gt h
      nlinarith
    · have hcSquareLower : (68938 / 90000 : ℝ) ^ 2 <
          Real.cos (2 * Real.pi / 9) ^ 2 := by
        nlinarith [mul_pos
          (sub_pos.mpr hcosBounds.1)
          (add_pos hcosPos (by norm_num : (0 : ℝ) < 68938 / 90000))]
      by_contra h
      have hsGe :
          (6430 / 10000 : ℝ) ≤ Real.sin (2 * Real.pi / 9) :=
        le_of_not_gt h
      nlinarith
  have hx := _motion.uniformHorizontalMotion
  rw [_readouts.horizontalDistanceMeters, hangle] at hx
  have hy := _motion.constantGravityVerticalMotion
  rw [_readouts.hoopHeightMeters, _readouts.releaseHeightMeters,
    _gravity, hangle] at hy
  norm_num at hx hy
  have ht :
      timeInSeconds setup.timeToHoop =
        10 /
          (speedInMetersPerSecond setup.launchSpeed *
            Real.cos (2 * Real.pi / 9)) := by
    rw [eq_div_iff (mul_ne_zero
      (ne_of_gt _physical.launchSpeedPositive) (ne_of_gt hcosPos))]
    nlinarith [hx]
  rw [ht] at hy
  field_simp [ne_of_gt _physical.launchSpeedPositive,
    ne_of_gt hcosPos] at hy
  have hspeedRelation :
      speedInMetersPerSecond setup.launchSpeed ^ 2 *
          (20 * Real.cos (2 * Real.pi / 9) *
              Real.sin (2 * Real.pi / 9) -
            (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2) =
        980 := by
    nlinarith [hy]
  have hcosSinLower :
      (68938 / 90000 : ℝ) * (6426 / 10000 : ℝ) <
        Real.cos (2 * Real.pi / 9) * Real.sin (2 * Real.pi / 9) := by
    nlinarith [mul_pos
      (sub_pos.mpr hcosBounds.1) hsinPos,
      mul_pos (by norm_num : (0 : ℝ) < 68938 / 90000)
        (sub_pos.mpr hsinBounds.1)]
  have hcosSinUpper :
      Real.cos (2 * Real.pi / 9) * Real.sin (2 * Real.pi / 9) <
        (68952 / 90000 : ℝ) * (6430 / 10000 : ℝ) := by
    nlinarith [mul_pos
      (sub_pos.mpr hcosBounds.2) hsinPos,
      mul_pos (by norm_num : (0 : ℝ) < 68952 / 90000)
        (sub_pos.mpr hsinBounds.2)]
  have hcosSquareLower :
      (68938 / 90000 : ℝ) ^ 2 <
        Real.cos (2 * Real.pi / 9) ^ 2 := by
    nlinarith [mul_pos
      (sub_pos.mpr hcosBounds.1)
      (add_pos hcosPos (by norm_num : (0 : ℝ) < 68938 / 90000))]
  have hcosSquareUpper :
      Real.cos (2 * Real.pi / 9) ^ 2 <
        (68952 / 90000 : ℝ) ^ 2 := by
    nlinarith [mul_pos
      (sub_pos.mpr hcosBounds.2)
      (add_pos hcosPos (by norm_num : (0 : ℝ) < 68952 / 90000))]
  have hfactorLower :
      (8611 / 1000 : ℝ) <
        20 * Real.cos (2 * Real.pi / 9) *
              Real.sin (2 * Real.pi / 9) -
            (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2 := by
    nlinarith
  have hfactorUpper :
      20 * Real.cos (2 * Real.pi / 9) *
              Real.sin (2 * Real.pi / 9) -
            (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2 <
        (8621 / 1000 : ℝ) := by
    nlinarith
  constructor
  · by_contra h
    have hvLe :
        speedInMetersPerSecond setup.launchSpeed ≤ (213 / 20 : ℝ) :=
      le_of_not_gt h
    have hvSquareLe :
        speedInMetersPerSecond setup.launchSpeed ^ 2 ≤
          (213 / 20 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hvLe)
        (add_nonneg _physical.launchSpeedPositive.le
          (by norm_num : (0 : ℝ) ≤ 213 / 20))]
    have hproductLt :
        speedInMetersPerSecond setup.launchSpeed ^ 2 *
            (20 * Real.cos (2 * Real.pi / 9) *
                Real.sin (2 * Real.pi / 9) -
              (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2) <
          (213 / 20 : ℝ) ^ 2 * (8621 / 1000 : ℝ) := by
      calc
        _ < speedInMetersPerSecond setup.launchSpeed ^ 2 *
              (8621 / 1000 : ℝ) :=
            mul_lt_mul_of_pos_left hfactorUpper
              (sq_pos_of_pos _physical.launchSpeedPositive)
        _ ≤ (213 / 20 : ℝ) ^ 2 * (8621 / 1000 : ℝ) :=
            mul_le_mul_of_nonneg_right hvSquareLe (by norm_num)
    rw [hspeedRelation] at hproductLt
    norm_num at hproductLt
  · by_contra h
    have hvGe :
        (215 / 20 : ℝ) ≤ speedInMetersPerSecond setup.launchSpeed :=
      le_of_not_gt h
    have hvSquareGe :
        (215 / 20 : ℝ) ^ 2 ≤
          speedInMetersPerSecond setup.launchSpeed ^ 2 := by
      nlinarith
    have hproductGt :
        (215 / 20 : ℝ) ^ 2 * (8611 / 1000 : ℝ) <
          speedInMetersPerSecond setup.launchSpeed ^ 2 *
            (20 * Real.cos (2 * Real.pi / 9) *
                Real.sin (2 * Real.pi / 9) -
              (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2) := by
      calc
        _ < (215 / 20 : ℝ) ^ 2 *
              (20 * Real.cos (2 * Real.pi / 9) *
                  Real.sin (2 * Real.pi / 9) -
                (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2) :=
            mul_lt_mul_of_pos_left hfactorLower (by norm_num)
        _ ≤ speedInMetersPerSecond setup.launchSpeed ^ 2 *
              (20 * Real.cos (2 * Real.pi / 9) *
                  Real.sin (2 * Real.pi / 9) -
                (21 / 10 : ℝ) * Real.cos (2 * Real.pi / 9) ^ 2) :=
            mul_le_mul_of_nonneg_right hvSquareGe
              (le_trans (by norm_num) hfactorLower.le)
    rw [hspeedRelation] at hproductGt
    norm_num at hproductGt

/-!
The required launch speed agrees to the displayed precision with
`10.7 m/s`, answer C, and C is the closest of the four printed choices.

This formalizes `thm:physics:phyx_mini_0689:target`.
-/
theorem problem_phyx_mini_0689
    (setup : BasketballShotSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_figure : MatchesPrimaryBasketballFigure setup)
    (_physical : HasPhysicalShotParameters setup)
    (_motion : SatisfiesIdealProjectileMotionToHoop setup) :
    MatchesDisplayedSpeed setup .C ∧
      IsClosestDisplayedChoice setup .C := by
  have hbounds :=
    requiredLaunchSpeed_bounds setup _readouts _gravity _physical _motion
  have hmatches : MatchesDisplayedSpeed setup .C := by
    change
      |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
        1 / 20
    rw [abs_le]
    constructor <;> nlinarith [hbounds.1, hbounds.2]
  refine ⟨hmatches, ?_⟩
  change ∀ otherChoice : AnswerChoice,
    |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
      |speedInMetersPerSecond setup.launchSpeed -
        otherChoice.speedInMetersPerSecond|
  intro otherChoice
  change
    |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
      1 / 20 at hmatches
  cases otherChoice with
  | A =>
      change
        |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
          |speedInMetersPerSecond setup.launchSpeed - (66 / 10 : ℝ)|
      nth_rewrite 2 [abs_of_nonneg (by nlinarith [hbounds.1])]
      linarith
  | B =>
      change
        |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
          |speedInMetersPerSecond setup.launchSpeed - (82 / 10 : ℝ)|
      nth_rewrite 2 [abs_of_nonneg (by nlinarith [hbounds.1])]
      linarith
  | C =>
      exact le_rfl
  | D =>
      change
        |speedInMetersPerSecond setup.launchSpeed - (107 / 10 : ℝ)| ≤
          |speedInMetersPerSecond setup.launchSpeed - (28 / 10 : ℝ)|
      nth_rewrite 2 [abs_of_nonneg (by nlinarith [hbounds.1])]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0689
