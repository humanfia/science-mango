import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0796

open Dimension

/-!
# Launch angle for maximum projectile range

A projectile is launched from the origin and returns to the launch height in
uniform downward gravity, with aerodynamic drag neglected.  For a fixed
positive launch speed, the requested quantity is the launch angle in the
interval from `0 degrees` through `90 degrees` that gives the greatest
horizontal range.

The supplied figure is an illustrative member of this family: it prints
`v₀ = 37.0 m/s` and `α₀ = 53.1 degrees`, marks a rising point at `t = 2.00 s`,
and labels the apex by `t₁`, `v₁`, and `h` and the landing point by `t₂`, `R`,
and `v₂`.  Its `53.1 degree` angle is kept separate from the angle optimized
in the theorem.

Lengths, durations, speed magnitudes, vector positions, vector velocities,
and gravitational acceleration are represented by unit-independent Physlib
quantities.  Real numbers occur only as coherent SI readouts, dimensionless
angle representatives, schematic drawing coordinates, and displayed answer
values.

Assumption/target split:

* governing laws: the constant-gravity horizontal and vertical position and
  velocity equations, same-height landing, and the interpretation of range as
  horizontal landing displacement;
* previous-part results: none (the range formula below is a derived lemma, not
  a premise);
* figure/data readouts: origin launch, `37.0 m/s`, `53.1 degrees`, the marked
  `2.00 s` point, the apex and landing labels, axes, arrows, and dashed path;
* current target: `45 degrees` is the unique range-maximizing angle and hence
  uniquely matches answer choice B.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length such as the range or maximum height. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative launch-speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed planar position vector. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful
    (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar velocity vector. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical elapsed time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a gravitational-acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a planar position in Cartesian metres. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Read a planar velocity in Cartesian metres per second. -/
def velocityInMetersPerSecond (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (velocity UnitChoices.SI).val

/-- Convert a degree readout to Mathlib's angle modulo `2 * π`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical model and primary-image vocabulary -/

/-- The idealized mechanics model used by the textbook range question. -/
inductive ProjectileModel where
  | uniformDownwardGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- Distinguished points visible along the dashed trajectory. -/
inductive FigurePoint where
  | launchOrigin
  | markedAtTwoSeconds
  | apex
  | landing
  deriving DecidableEq, Fintype, Repr

/-- Velocity arrows and their literal names in the supplied figure. -/
inductive FigureVelocityLabel where
  | initialVZero
  | intermediateV
  | apexVOne
  | landingVTwo
  deriving DecidableEq, Fintype, Repr

/-- Visible graphical elements in image `796.png`. -/
inductive FigureElement where
  | horizontalXAxis
  | verticalYAxis
  | dashedParabolicTrajectory
  | initialVelocityArrow
  | intermediateVelocityArrow
  | apexVelocityArrow
  | landingVelocityArrow
  | heightGuide
  | rangeGuide
  deriving DecidableEq, Fintype, Repr

/-- Literal numerical and symbolic labels printed in image `796.png`. -/
inductive FigureLabel where
  | initialSpeed37MetersPerSecond
  | initialAngle53Point1Degrees
  | horizontalCoordinateXUnknown
  | verticalCoordinateYUnknown
  | markedTime2Seconds
  | apexTimeTOneUnknown
  | apexVelocityVOne
  | maximumHeightHUnknown
  | flightTimeTTwoUnknown
  | rangeRUnknown
  | landingVelocityVTwo
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and schematic information transcribed from the raster.  The
schematic coordinates describe the drawing only; physical coordinates,
times, lengths, and velocities remain unit-aware quantities.
-/
structure ProjectileFigure where
  showsElement : FigureElement → Bool
  showsLabel : FigureLabel → Bool
  horizontalCoordinate : FigurePoint → ℝ
  verticalCoordinate : FigurePoint → ℝ
  timeAtPoint : FigurePoint → TimeQuantity
  velocityByLabel : FigureVelocityLabel → PlanarVelocityQuantity
  velocityArrowBase : FigureVelocityLabel → FigurePoint
  dashedPathStart : FigurePoint
  dashedPathEnd : FigurePoint
  heightLabelQuantity : LengthQuantity
  rangeLabelQuantity : LengthQuantity

/-!
A fixed-speed family of same-height projectile launches.  The trajectory,
flight time, and horizontal range are indexed by the candidate physical
launch angle.  The angle shown in the supplied figure is a separate field and
does not define the maximizing angle.
-/
structure ProjectileRangeSetup where
  model : ProjectileModel
  initialSpeed : SpeedQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  launchPosition : PlanarPositionQuantity
  launchTime : TimeQuantity
  figureLaunchAngle : Real.Angle
  markedTime : TimeQuantity
  apexTime : TimeQuantity
  figureFlightTime : TimeQuantity
  maximumHeight : LengthQuantity
  trajectoryPosition : Real.Angle → TimeQuantity → PlanarPositionQuantity
  trajectoryVelocity : Real.Angle → TimeQuantity → PlanarVelocityQuantity
  flightTime : Real.Angle → TimeQuantity
  horizontalRange : Real.Angle → LengthQuantity
  figure : ProjectileFigure

/-! ## Figure evidence, numerical readouts, physical branch, and laws -/

/-- Candidate launch angles run from the horizontal through the vertical. -/
def IsAdmissibleLaunchAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/-!
The numerical values and physical point identifications printed in the figure.
The `53.1 degree` figure angle is illustrative and is not asserted to maximize
the range.
-/
structure MatchesProblemReadouts (setup : ProjectileRangeSetup) : Prop where
  usesIdealProjectileModel :
    setup.model = .uniformDownwardGravityNegligibleDrag
  initialSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 37
  figureLaunchAngleDegrees :
    setup.figureLaunchAngle = degrees ((531 : ℝ) / 10)
  launchTimeSeconds : timeInSeconds setup.launchTime = 0
  markedTimeSeconds : timeInSeconds setup.markedTime = 2
  figureFlightTimeIsFamilyFlightTime :
    setup.figureFlightTime = setup.flightTime setup.figureLaunchAngle
  launchAtPhysicalOriginX :
    positionInMeters setup.launchPosition xAxis = 0
  launchAtPhysicalOriginY :
    positionInMeters setup.launchPosition yAxis = 0
  markedPointAfterLaunch :
    timeInSeconds setup.launchTime < timeInSeconds setup.markedTime
  markedPointBeforeApex :
    timeInSeconds setup.markedTime < timeInSeconds setup.apexTime
  apexBeforeLanding :
    timeInSeconds setup.apexTime < timeInSeconds setup.figureFlightTime
  apexDefinesMaximumHeight :
    positionInMeters
          (setup.trajectoryPosition setup.figureLaunchAngle setup.apexTime)
          yAxis -
        positionInMeters setup.launchPosition yAxis =
      lengthInMeters setup.maximumHeight
  apexHasZeroVerticalVelocity :
    velocityInMetersPerSecond
        (setup.trajectoryVelocity setup.figureLaunchAngle setup.apexTime)
        yAxis = 0

/-!
Primary-image evidence for the axes, dashed path, labelled points, and four
velocity arrows.  No schematic coordinate is treated as a calibrated length.
-/
structure MatchesPrimaryFigure (setup : ProjectileRangeSetup) : Prop where
  everyElementShown : ∀ element, setup.figure.showsElement element = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  launchAtSchematicOriginX :
    setup.figure.horizontalCoordinate .launchOrigin = 0
  launchAtSchematicOriginY :
    setup.figure.verticalCoordinate .launchOrigin = 0
  pointsRunLeftToRight :
    setup.figure.horizontalCoordinate .launchOrigin <
        setup.figure.horizontalCoordinate .markedAtTwoSeconds ∧
      setup.figure.horizontalCoordinate .markedAtTwoSeconds <
        setup.figure.horizontalCoordinate .apex ∧
      setup.figure.horizontalCoordinate .apex <
        setup.figure.horizontalCoordinate .landing
  apexAboveMarkedPoint :
    setup.figure.verticalCoordinate .markedAtTwoSeconds <
      setup.figure.verticalCoordinate .apex
  landingReturnsToLaunchLevel :
    setup.figure.verticalCoordinate .landing =
      setup.figure.verticalCoordinate .launchOrigin
  markedPointAboveLaunchLevel :
    setup.figure.verticalCoordinate .launchOrigin <
      setup.figure.verticalCoordinate .markedAtTwoSeconds
  dashedPathRunsFromLaunchToLanding :
    setup.figure.dashedPathStart = .launchOrigin ∧
      setup.figure.dashedPathEnd = .landing
  pointTimesMatchPhysicalLabels :
    setup.figure.timeAtPoint .launchOrigin = setup.launchTime ∧
      setup.figure.timeAtPoint .markedAtTwoSeconds = setup.markedTime ∧
      setup.figure.timeAtPoint .apex = setup.apexTime ∧
      setup.figure.timeAtPoint .landing = setup.figureFlightTime
  velocityArrowsHaveShownBases :
    setup.figure.velocityArrowBase .initialVZero = .launchOrigin ∧
      setup.figure.velocityArrowBase .intermediateV = .markedAtTwoSeconds ∧
      setup.figure.velocityArrowBase .apexVOne = .apex ∧
      setup.figure.velocityArrowBase .landingVTwo = .landing
  velocityArrowsMatchTrajectory :
    setup.figure.velocityByLabel .initialVZero =
        setup.trajectoryVelocity setup.figureLaunchAngle setup.launchTime ∧
      setup.figure.velocityByLabel .intermediateV =
        setup.trajectoryVelocity setup.figureLaunchAngle setup.markedTime ∧
      setup.figure.velocityByLabel .apexVOne =
        setup.trajectoryVelocity setup.figureLaunchAngle setup.apexTime ∧
      setup.figure.velocityByLabel .landingVTwo =
        setup.trajectoryVelocity setup.figureLaunchAngle setup.figureFlightTime
  heightLabelMatchesPhysicalHeight :
    setup.figure.heightLabelQuantity = setup.maximumHeight
  rangeLabelMatchesPhysicalRange :
    setup.figure.rangeLabelQuantity =
      setup.horizontalRange setup.figureLaunchAngle

/-!
Positivity and endpoint-branch conditions.  At a horizontal launch the
same-height flight is the zero-duration endpoint; every admissible angle
strictly above the horizontal uses the later, positive landing time.
-/
structure HasPhysicalProjectileBranch (setup : ProjectileRangeSetup) : Prop where
  initialSpeedPositive : 0 < speedInMetersPerSecond setup.initialSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  horizontalLaunchEndsAtLaunchTime :
    setup.flightTime (degrees 0) = setup.launchTime
  laterLandingForPositiveAngles : ∀ angle,
    IsAdmissibleLaunchAngle angle →
      0 < angle.toReal →
        timeInSeconds setup.launchTime <
          timeInSeconds (setup.flightTime angle)

/-!
The standard no-drag, constant-gravity projectile equations in coherent SI
readouts.  They are stated for every admissible candidate angle at the fixed
launch speed.  The final two fields say only that a flight ends at its launch
height and that `R` measures its horizontal displacement; neither identifies
the maximizing angle.
-/
structure SatisfiesUniformGravityProjectileLaws
    (setup : ProjectileRangeSetup) : Prop where
  startsAtLaunchPosition : ∀ angle,
    IsAdmissibleLaunchAngle angle →
      setup.trajectoryPosition angle setup.launchTime = setup.launchPosition
  horizontalPosition : ∀ angle time,
    IsAdmissibleLaunchAngle angle →
      positionInMeters (setup.trajectoryPosition angle time) xAxis -
          positionInMeters setup.launchPosition xAxis =
        speedInMetersPerSecond setup.initialSpeed *
          Real.Angle.cos angle *
          (timeInSeconds time - timeInSeconds setup.launchTime)
  verticalPosition : ∀ angle time,
    IsAdmissibleLaunchAngle angle →
      positionInMeters (setup.trajectoryPosition angle time) yAxis -
          positionInMeters setup.launchPosition yAxis =
        speedInMetersPerSecond setup.initialSpeed *
            Real.Angle.sin angle *
            (timeInSeconds time - timeInSeconds setup.launchTime) -
          (1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (timeInSeconds time - timeInSeconds setup.launchTime) ^ 2
  horizontalVelocity : ∀ angle time,
    IsAdmissibleLaunchAngle angle →
      velocityInMetersPerSecond (setup.trajectoryVelocity angle time) xAxis =
        speedInMetersPerSecond setup.initialSpeed * Real.Angle.cos angle
  verticalVelocity : ∀ angle time,
    IsAdmissibleLaunchAngle angle →
      velocityInMetersPerSecond (setup.trajectoryVelocity angle time) yAxis =
        speedInMetersPerSecond setup.initialSpeed * Real.Angle.sin angle -
          accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (timeInSeconds time - timeInSeconds setup.launchTime)
  landsAtLaunchHeight : ∀ angle,
    IsAdmissibleLaunchAngle angle →
      positionInMeters
          (setup.trajectoryPosition angle (setup.flightTime angle)) yAxis =
        positionInMeters setup.launchPosition yAxis
  rangeIsLandingDisplacement : ∀ angle,
    IsAdmissibleLaunchAngle angle →
      positionInMeters
            (setup.trajectoryPosition angle (setup.flightTime angle)) xAxis -
          positionInMeters setup.launchPosition xAxis =
        lengthInMeters (setup.horizontalRange angle)

/-!
Eliminating the positive flight time from the same-height endpoint equation
gives the usual range relation.  This is a derived conclusion from the model,
not an assumption and not the requested maximization result.
-/
lemma horizontalRangeFormula
    (setup : ProjectileRangeSetup)
    (h_branch : HasPhysicalProjectileBranch setup)
    (h_laws : SatisfiesUniformGravityProjectileLaws setup)
    (angle : Real.Angle)
    (h_angle : IsAdmissibleLaunchAngle angle) :
    lengthInMeters (setup.horizontalRange angle) =
      speedInMetersPerSecond setup.initialSpeed ^ 2 *
        Real.Angle.sin (2 • angle) /
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
  by_cases h_zero : angle.toReal = 0
  · have h_angle_zero : angle = 0 :=
      Real.Angle.toReal_eq_zero_iff.mp h_zero
    subst angle
    have h_flight :
        setup.flightTime 0 = setup.launchTime := by
      simpa [degrees] using h_branch.horizontalLaunchEndsAtLaunchTime
    calc
      lengthInMeters (setup.horizontalRange 0) =
          positionInMeters
                (setup.trajectoryPosition 0 (setup.flightTime 0)) xAxis -
            positionInMeters setup.launchPosition xAxis := by
              symm
              exact h_laws.rangeIsLandingDisplacement 0 h_angle
      _ = speedInMetersPerSecond setup.initialSpeed *
            Real.Angle.cos 0 *
            (timeInSeconds (setup.flightTime 0) -
              timeInSeconds setup.launchTime) :=
          h_laws.horizontalPosition 0 (setup.flightTime 0) h_angle
      _ = speedInMetersPerSecond setup.initialSpeed ^ 2 *
            Real.Angle.sin (2 • (0 : Real.Angle)) /
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration := by
          simp [h_flight]
  · have h_angle_pos : 0 < angle.toReal :=
      lt_of_le_of_ne h_angle.1 (Ne.symm h_zero)
    have h_time_pos :
        0 <
          timeInSeconds (setup.flightTime angle) -
            timeInSeconds setup.launchTime := by
      linarith [h_branch.laterLandingForPositiveAngles angle h_angle h_angle_pos]
    have h_vertical :=
      h_laws.verticalPosition angle (setup.flightTime angle) h_angle
    rw [h_laws.landsAtLaunchHeight angle h_angle] at h_vertical
    have h_time_relation :
        accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (timeInSeconds (setup.flightTime angle) -
              timeInSeconds setup.launchTime) =
          2 * speedInMetersPerSecond setup.initialSpeed *
            Real.Angle.sin angle := by
      nlinarith
    calc
      lengthInMeters (setup.horizontalRange angle) =
          positionInMeters
                (setup.trajectoryPosition angle (setup.flightTime angle)) xAxis -
            positionInMeters setup.launchPosition xAxis := by
              symm
              exact h_laws.rangeIsLandingDisplacement angle h_angle
      _ = speedInMetersPerSecond setup.initialSpeed *
            Real.Angle.cos angle *
            (timeInSeconds (setup.flightTime angle) -
              timeInSeconds setup.launchTime) :=
          h_laws.horizontalPosition angle (setup.flightTime angle) h_angle
      _ = speedInMetersPerSecond setup.initialSpeed ^ 2 *
            Real.Angle.sin (2 • angle) /
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration := by
          rw [Real.Angle.sin_two_nsmul]
          simp only [nsmul_eq_mul, Nat.cast_ofNat]
          field_simp [ne_of_gt h_branch.gravityPositive]
          linear_combination
            speedInMetersPerSecond setup.initialSpeed *
              Real.Angle.cos angle * h_time_relation

/-! ## Range maximization and multiple-choice answers -/

/-- A candidate angle gives at least as much range as every admissible angle. -/
def MaximizesHorizontalRange
    (setup : ProjectileRangeSetup) (angle : Real.Angle) : Prop :=
  IsAdmissibleLaunchAngle angle ∧
    ∀ candidate, IsAdmissibleLaunchAngle candidate →
      lengthInMeters (setup.horizontalRange candidate) ≤
        lengthInMeters (setup.horizontalRange angle)

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical degree values printed beside the answer choices. -/
def AnswerChoice.degreeValue : AnswerChoice → ℝ
  | .A => 30
  | .B => 45
  | .C => 60
  | .D => 90

/-- The physical launch angle represented by an answer choice. -/
noncomputable def AnswerChoice.angle (choice : AnswerChoice) : Real.Angle :=
  degrees choice.degreeValue

/-- An answer choice matches exactly when its angle maximizes the range. -/
def AnswerChoice.MatchesMaximumRange
    (choice : AnswerChoice) (setup : ProjectileRangeSetup) : Prop :=
  MaximizesHorizontalRange setup choice.angle

/--
For a fixed positive launch speed in the ideal same-height projectile model,
`45 degrees` is the unique angle between `0 degrees` and `90 degrees` that
maximizes horizontal range.  Therefore choice B, and no other displayed
choice, matches the maximum.

This formalizes `thm:physics:phyx_mini_0796:target`.
-/
theorem problem_phyx_mini_0796
    (setup : ProjectileRangeSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_branch : HasPhysicalProjectileBranch setup)
    (h_laws : SatisfiesUniformGravityProjectileLaws setup) :
    MaximizesHorizontalRange setup (degrees 45) ∧
      (∀ angle, MaximizesHorizontalRange setup angle →
        angle = degrees 45) ∧
      AnswerChoice.B.MatchesMaximumRange setup ∧
      (∀ choice, choice.MatchesMaximumRange setup →
        choice = AnswerChoice.B) := by
  have h_degrees_45 :
      degrees 45 = ((Real.pi / 4 : ℝ) : Real.Angle) := by
    rw [degrees]
    exact congrArg (fun value : ℝ => (value : Real.Angle)) (by ring)
  have h_toReal_45 : (degrees 45).toReal = Real.pi / 4 := by
    rw [h_degrees_45, Real.Angle.toReal_coe_eq_self_iff]
    constructor <;> linarith [Real.pi_pos]
  have h_admissible_45 : IsAdmissibleLaunchAngle (degrees 45) := by
    rw [IsAdmissibleLaunchAngle, h_toReal_45]
    constructor <;> linarith [Real.pi_pos]
  have h_twice_45 :
      (2 : ℕ) • degrees 45 =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [h_degrees_45, ← Real.Angle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have h_sin_twice_45 :
      Real.Angle.sin ((2 : ℕ) • degrees 45) = 1 := by
    rw [h_twice_45, Real.Angle.sin_coe, Real.sin_pi_div_two]
  have h_maximizes_45 :
      MaximizesHorizontalRange setup (degrees 45) := by
    refine ⟨h_admissible_45, ?_⟩
    intro candidate h_candidate
    rw [horizontalRangeFormula setup h_branch h_laws candidate h_candidate,
      horizontalRangeFormula setup h_branch h_laws (degrees 45)
        h_admissible_45,
      h_sin_twice_45]
    apply (div_le_div_iff₀ h_branch.gravityPositive
      h_branch.gravityPositive).2
    apply mul_le_mul_of_nonneg_right
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left
          (show Real.Angle.sin ((2 : ℕ) • candidate) ≤ 1 by
            simpa only [Real.Angle.sin_toReal] using
              Real.sin_le_one (((2 : ℕ) • candidate).toReal))
          (sq_nonneg (speedInMetersPerSecond setup.initialSpeed))
    · exact h_branch.gravityPositive.le
  have h_unique :
      ∀ angle, MaximizesHorizontalRange setup angle →
        angle = degrees 45 := by
    intro angle h_maximizes
    have h_range_comparison :=
      h_maximizes.2 (degrees 45) h_admissible_45
    rw [horizontalRangeFormula setup h_branch h_laws (degrees 45)
          h_admissible_45,
      horizontalRangeFormula setup h_branch h_laws angle h_maximizes.1,
      h_sin_twice_45] at h_range_comparison
    have h_coefficient_positive :
        0 <
          speedInMetersPerSecond setup.initialSpeed ^ 2 /
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration := by
      exact div_pos (sq_pos_of_pos h_branch.initialSpeedPositive)
        h_branch.gravityPositive
    have h_sin_ge_one :
        1 ≤ Real.Angle.sin ((2 : ℕ) • angle) := by
      have h_scaled :
          (speedInMetersPerSecond setup.initialSpeed ^ 2 /
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration) * 1 ≤
            (speedInMetersPerSecond setup.initialSpeed ^ 2 /
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration) *
              Real.Angle.sin ((2 : ℕ) • angle) := by
        convert h_range_comparison using 1 <;> ring
      nlinarith
    have h_sin_le_one :
        Real.Angle.sin ((2 : ℕ) • angle) ≤ 1 := by
      simpa only [Real.Angle.sin_toReal] using
        Real.sin_le_one (((2 : ℕ) • angle).toReal)
    have h_sin_eq_one :
        Real.Angle.sin ((2 : ℕ) • angle) = 1 :=
      le_antisymm h_sin_le_one h_sin_ge_one
    rw [Real.Angle.sin_two_nsmul] at h_sin_eq_one
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h_sin_eq_one
    have h_sin_eq_cos :
        Real.Angle.sin angle = Real.Angle.cos angle := by
      nlinarith [Real.Angle.cos_sq_add_sin_sq angle,
        sq_nonneg (Real.Angle.sin angle - Real.Angle.cos angle)]
    have h_real_sines :
        Real.sin angle.toReal =
          Real.sin (Real.pi / 2 - angle.toReal) := by
      simpa only [Real.Angle.sin_toReal, Real.Angle.cos_toReal,
        Real.sin_pi_div_two_sub] using h_sin_eq_cos
    have h_angle_mem :
        angle.toReal ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos, h_maximizes.1.1]
      · exact h_maximizes.1.2
    have h_complement_mem :
        Real.pi / 2 - angle.toReal ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos, h_maximizes.1.1,
        h_maximizes.1.2]
    have h_toReal_eq :
        angle.toReal = Real.pi / 2 - angle.toReal :=
      Real.injOn_sin h_angle_mem h_complement_mem h_real_sines
    apply Real.Angle.toReal_injective
    rw [h_toReal_45]
    linarith
  refine ⟨h_maximizes_45, h_unique, ?_, ?_⟩
  · simpa [AnswerChoice.MatchesMaximumRange, AnswerChoice.angle,
      AnswerChoice.degreeValue] using h_maximizes_45
  · intro choice h_choice
    have h_choice_angle : choice.angle = degrees 45 :=
      h_unique choice.angle h_choice
    have h_degrees_toReal
        {value : ℝ} (h_value_nonnegative : 0 ≤ value)
        (h_value_le_180 : value ≤ 180) :
        (degrees value).toReal = value * Real.pi / 180 := by
      rw [degrees, Real.Angle.toReal_coe_eq_self_iff]
      constructor
      · have h_product_nonnegative :
            0 ≤ value * Real.pi :=
          mul_nonneg h_value_nonnegative Real.pi_pos.le
        linarith [Real.pi_pos]
      · have h_product_le :
            value * Real.pi ≤ 180 * Real.pi :=
          mul_le_mul_of_nonneg_right h_value_le_180 Real.pi_pos.le
        linarith
    cases choice with
    | A =>
        exfalso
        have h := congrArg Real.Angle.toReal h_choice_angle
        simp only [AnswerChoice.angle, AnswerChoice.degreeValue] at h
        rw [h_degrees_toReal (by norm_num) (by norm_num),
          h_toReal_45] at h
        nlinarith [Real.pi_pos]
    | B => rfl
    | C =>
        exfalso
        have h := congrArg Real.Angle.toReal h_choice_angle
        simp only [AnswerChoice.angle, AnswerChoice.degreeValue] at h
        rw [h_degrees_toReal (by norm_num) (by norm_num),
          h_toReal_45] at h
        nlinarith [Real.pi_pos]
    | D =>
        exfalso
        have h := congrArg Real.Angle.toReal h_choice_angle
        simp only [AnswerChoice.angle, AnswerChoice.degreeValue] at h
        rw [h_degrees_toReal (by norm_num) (by norm_num),
          h_toReal_45] at h
        nlinarith [Real.pi_pos]

end PhyXMiniProblems.ProblemPhyXMini0796
