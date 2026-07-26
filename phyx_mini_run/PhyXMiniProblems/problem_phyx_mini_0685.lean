import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0685

open Dimension

/-!
# Projectile returned to a rooftop playground

A passerby launches a ball from street level toward a school roof.  The roof
is `6.00 m` above the street, and a one-metre railing makes the wall top marked
`h` lie `7.00 m` above the street.  The launch point is the horizontal distance
`d = 24.0 m` from the wall, the launch angle is `theta = 53.0 degrees`, and the
ball reaches the vertical line through the wall after `2.20 s`.  The requested
quantity is the horizontal distance from that wall to the later roof impact.

Physical lengths, durations, speeds, and accelerations below use Physlib's
unit-independent `Dimensionful (WithDim ...)` quantities.  Real numbers occur
only as coherent SI readouts, dimensionless trigonometric values, schematic
figure coordinates, and displayed multiple-choice values.

The landing distance is an independent field of the setup.  It is constrained
by general projectile and impact-geometry laws, but no premise fixes it to
`2.79 m` or selects answer C.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of speed, `L T^-1`. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional physical displacement or coordinate. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration measured from launch. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative launch-speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre readout of a signed displacement coordinate. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image transcription -/

/-- The idealized environment in which the standard projectile equations hold. -/
inductive ProjectileModel where
  | constantGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- The physical place from which the ball is returned. -/
inductive LaunchLocation where
  | street
  deriving DecidableEq, Repr

/-- The surface on which the question says the ball later lands. -/
inductive LandingSurface where
  | playgroundRoof
  deriving DecidableEq, Repr

/-- Physical objects visibly represented in image `685.png`. -/
inductive FigureObject where
  | passerby
  | ball
  | building
  | rooftopPlayground
  | railing
  | leftRoofPerson
  | rightRoofPerson
  deriving DecidableEq, Fintype, Repr

/-- Mathematical labels visibly printed in the primary image. -/
inductive FigureLabel where
  | launchAngleTheta
  | wallTopHeightH
  | launchToWallDistanceD
  deriving DecidableEq, Fintype, Repr

/-- Schematic points needed to retain the spatial relations in the figure. -/
inductive FigureAnchor where
  | launchPoint
  | wallBase
  | railingTop
  | roofAtWall
  | roofRightEnd
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and schematic-coordinate evidence from the primary raster.
Coordinates are dimensionless drawing coordinates, not measured lengths.
-/
structure RooftopProjectileFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  horizontalPosition : FigureAnchor → ℝ
  verticalPosition : FigureAnchor → ℝ
  showsDashedParabolicTrajectory : Bool
  launchArrowPointsUpAndRight : Bool
  heightArrowRunsStreetToRailingTop : Bool
  distanceArrowRunsLaunchPointToWall : Bool

/-!
The independent physical quantities in the projectile experiment.  The two
coordinate functions give signed displacements from the street-level launch
point as functions of elapsed physical time.  In particular,
`landingDistanceFromWall` is not defined from an answer choice.
-/
structure RooftopProjectileSetup where
  model : ProjectileModel
  launchLocation : LaunchLocation
  landingSurface : LandingSurface
  roofHeight : LengthQuantity
  wallTopHeight : LengthQuantity
  railingHeight : LengthQuantity
  launchToWallDistance : LengthQuantity
  timeToWallVertical : TimeQuantity
  launchAngle : Real.Angle
  launchSpeed : SpeedQuantity
  gravitationalAcceleration : AccelerationQuantity
  landingTime : TimeQuantity
  landingDistanceFromWall : LengthQuantity
  horizontalDisplacement : TimeQuantity → SignedLengthQuantity
  verticalDisplacement : TimeQuantity → SignedLengthQuantity
  figure : RooftopProjectileFigure

/-!
Every named object and label is shown.  The schematic positions say that the
launch occurs at street level to the left of the vertical wall, the roof lies
above the street and to the right of the wall, and the railing top marked `h`
lies above the roof.  No landing-distance readout occurs in the image.
-/
structure MatchesPrimaryFigure (setup : RooftopProjectileSetup) : Prop where
  everyNamedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyNamedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  launchIsLeftOfWall :
    setup.figure.horizontalPosition .launchPoint <
      setup.figure.horizontalPosition .wallBase
  wallIsVertical :
    setup.figure.horizontalPosition .wallBase =
        setup.figure.horizontalPosition .railingTop ∧
      setup.figure.horizontalPosition .wallBase =
        setup.figure.horizontalPosition .roofAtWall
  roofExtendsRightFromWall :
    setup.figure.horizontalPosition .roofAtWall <
      setup.figure.horizontalPosition .roofRightEnd
  launchAndWallBaseAtStreetLevel :
    setup.figure.verticalPosition .launchPoint =
      setup.figure.verticalPosition .wallBase
  roofAboveStreet :
    setup.figure.verticalPosition .wallBase <
      setup.figure.verticalPosition .roofAtWall
  railingTopAboveRoof :
    setup.figure.verticalPosition .roofAtWall <
      setup.figure.verticalPosition .railingTop
  dashedTrajectoryShown :
    setup.figure.showsDashedParabolicTrajectory = true
  launchArrowShownUpAndRight :
    setup.figure.launchArrowPointsUpAndRight = true
  heightArrowMatchesFigure :
    setup.figure.heightArrowRunsStreetToRailingTop = true
  distanceArrowMatchesFigure :
    setup.figure.distanceArrowRunsLaunchPointToWall = true

/-! ## Stated readouts, physical branch, and governing laws -/

/-- Convert a degree readout to a physical angle modulo `2 * pi`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- The qualitative scenario and numerical quantities stated in the prose. -/
structure MatchesProblemDescription (setup : RooftopProjectileSetup) : Prop where
  idealProjectileModel :
    setup.model = .constantGravityNegligibleDrag
  launchedFromStreet : setup.launchLocation = .street
  landsOnPlaygroundRoof : setup.landingSurface = .playgroundRoof
  roofHeightMeters : lengthInMeters setup.roofHeight = 6
  wallTopHeightMeters : lengthInMeters setup.wallTopHeight = 7
  railingHeightMeters : lengthInMeters setup.railingHeight = 1
  wallTopIsRoofPlusRailing :
    lengthInMeters setup.wallTopHeight =
      lengthInMeters setup.roofHeight + lengthInMeters setup.railingHeight
  launchToWallDistanceMeters :
    lengthInMeters setup.launchToWallDistance = 24
  launchAngleDegrees : setup.launchAngle = degrees 53
  timeToWallSeconds : timeInSeconds setup.timeToWallVertical = 11 / 5

/-!
The standard near-Earth value needed by the textbook projectile model.
It is a physical calibration, not a landing-distance assumption.
-/
structure UsesStandardNearEarthGravity
    (setup : RooftopProjectileSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-!
Positivity, ordering, and the upward/rightward branch depicted in the figure.
These conditions do not assign a numerical value to the landing distance.
-/
structure HasPhysicalProjectileParameters
    (setup : RooftopProjectileSetup) : Prop where
  roofHeightPositive : 0 < lengthInMeters setup.roofHeight
  wallTopHeightPositive : 0 < lengthInMeters setup.wallTopHeight
  railingHeightPositive : 0 < lengthInMeters setup.railingHeight
  launchToWallDistancePositive :
    0 < lengthInMeters setup.launchToWallDistance
  timeToWallPositive : 0 < timeInSeconds setup.timeToWallVertical
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  roofBelowRailingTop :
    lengthInMeters setup.roofHeight < lengthInMeters setup.wallTopHeight
  launchPointsRight : 0 < Real.Angle.cos setup.launchAngle
  launchPointsUp : 0 < Real.Angle.sin setup.launchAngle
  landingOccursAfterWall :
    timeInSeconds setup.timeToWallVertical < timeInSeconds setup.landingTime
  landingDistancePositive :
    0 < lengthInMeters setup.landingDistanceFromWall

/-!
The governing ideal-projectile relations in coherent SI readouts:

* horizontal displacement is uniform motion with velocity
  `v0 * cos(theta)`;
* vertical displacement is `v0 * sin(theta) * t - g * t^2 / 2`;
* at the observed `2.20 s`, the ball is vertically above the wall and clears
  the `7.00 m` railing top;
* at the later landing time, the vertical coordinate is the `6.00 m` roof
  height; and
* the landing distance is the horizontal displacement beyond the wall.

These are general physical and geometric laws.  They contain neither the
number `2.79` nor an answer-choice assertion.
-/
structure SatisfiesIdealProjectileLaws
    (setup : RooftopProjectileSetup) : Prop where
  uniformHorizontalMotion : ∀ duration : TimeQuantity,
    signedLengthInMeters (setup.horizontalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle * timeInSeconds duration
  verticalConstantGravityMotion : ∀ duration : TimeQuantity,
    signedLengthInMeters (setup.verticalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle * timeInSeconds duration -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          timeInSeconds duration ^ 2
  horizontallyAboveWallAtObservedTime :
    signedLengthInMeters
        (setup.horizontalDisplacement setup.timeToWallVertical) =
      lengthInMeters setup.launchToWallDistance
  clearsRailingAtWall :
    lengthInMeters setup.wallTopHeight <
      signedLengthInMeters
        (setup.verticalDisplacement setup.timeToWallVertical)
  landsAtRoofHeight :
    signedLengthInMeters (setup.verticalDisplacement setup.landingTime) =
      lengthInMeters setup.roofHeight
  landingDistanceIsMeasuredFromWall :
    signedLengthInMeters (setup.horizontalDisplacement setup.landingTime) =
      lengthInMeters setup.launchToWallDistance +
        lengthInMeters setup.landingDistanceFromWall

/-! ## Exact calculation and displayed answers -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance in metres printed beside each displayed answer label. -/
def answerDistanceInMeters : AnswerChoice → ℝ
  | .A => 286 / 100
  | .B => 312 / 100
  | .C => 279 / 100
  | .D => 213 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The later root of the roof-height quadratic, after eliminating the launch
speed using the measured horizontal wall-crossing time.
-/
noncomputable def computedLandingTimeInSeconds : ℝ :=
  let wallTime : ℝ := 11 / 5
  let horizontalSpeed : ℝ := 24 / wallTime
  let angle : Real.Angle := degrees 53
  let verticalSpeed : ℝ :=
    horizontalSpeed * Real.Angle.sin angle / Real.Angle.cos angle
  let gravity : ℝ := 49 / 5
  (verticalSpeed + Real.sqrt (verticalSpeed ^ 2 - 2 * gravity * 6)) / gravity

/-!
The exact unrounded horizontal distance beyond the wall predicted by the
stated data and the standard-gravity projectile model.  The independent setup
field is not definitionally equal to this expression.
-/
noncomputable def computedLandingDistanceInMeters : ℝ :=
  (24 / (11 / 5 : ℝ)) * (computedLandingTimeInSeconds - 11 / 5)

/-- Agreement with a displayed distance rounded to the nearest centimetre. -/
def MatchesDisplayedDistance
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters distance - answerDistanceInMeters choice| ≤ (1 : ℝ) / 200

/-- A displayed choice is at least as close as every other choice. -/
def IsClosestDisplayedDistance
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |lengthInMeters distance - answerDistanceInMeters choice| ≤
      |lengthInMeters distance - answerDistanceInMeters other|

/-- A displayed choice is the unique closest printed value. -/
def IsUniqueClosestDisplayedDistance
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedDistance distance choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedDistance distance other → other = choice

/-!
Eliminating the launch speed and selecting the later roof intersection gives
the exact expression above.  This is a derived conclusion rather than a field
of the physical-law premise.
-/
lemma landingDistance_eq_computedExpression
    (setup : RooftopProjectileSetup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesIdealProjectileLaws setup) :
    lengthInMeters setup.landingDistanceFromWall =
      computedLandingDistanceInMeters := by
  let v : ℝ := speedInMetersPerSecond setup.launchSpeed
  let s : ℝ := Real.Angle.sin setup.launchAngle
  let c : ℝ := Real.Angle.cos setup.launchAngle
  let t : ℝ := timeInSeconds setup.landingTime
  let w : ℝ := (120 / 11 : ℝ) * s / c

  have hc : 0 < c := by
    simpa [c] using _physical.launchPointsRight
  have ht : (11 / 5 : ℝ) < t := by
    simpa [t, _description.timeToWallSeconds] using
      _physical.landingOccursAfterWall

  have hhorizontal : v * c * (11 / 5 : ℝ) = 24 := by
    calc
      v * c * (11 / 5 : ℝ) =
          signedLengthInMeters
            (setup.horizontalDisplacement setup.timeToWallVertical) := by
              rw [_laws.uniformHorizontalMotion]
              simp only [v, c]
              rw [_description.timeToWallSeconds]
      _ = lengthInMeters setup.launchToWallDistance :=
        _laws.horizontallyAboveWallAtObservedTime
      _ = 24 := _description.launchToWallDistanceMeters
  have hvc : v * c = (120 / 11 : ℝ) := by
    norm_num at hhorizontal ⊢
    linarith
  have hvs : v * s = w := by
    apply (eq_div_iff hc.ne').2
    calc
      v * s * c = (v * c) * s := by ring
      _ = (120 / 11 : ℝ) * s := by rw [hvc]

  have hyWall :
      7 <
        v * s * (11 / 5 : ℝ) -
          (1 / 2 : ℝ) * (49 / 5 : ℝ) * (11 / 5 : ℝ) ^ 2 := by
    calc
      7 = lengthInMeters setup.wallTopHeight :=
        _description.wallTopHeightMeters.symm
      _ <
          signedLengthInMeters
            (setup.verticalDisplacement setup.timeToWallVertical) :=
        _laws.clearsRailingAtWall
      _ =
          v * s * (11 / 5 : ℝ) -
            (1 / 2 : ℝ) * (49 / 5 : ℝ) * (11 / 5 : ℝ) ^ 2 := by
        rw [_laws.verticalConstantGravityMotion]
        simp only [v, s]
        rw [_description.timeToWallSeconds,
          _gravity.gravityMetersPerSecondSquared]
  have hyLanding :
      v * s * t -
          (1 / 2 : ℝ) * (49 / 5 : ℝ) * t ^ 2 = 6 := by
    calc
      v * s * t -
          (1 / 2 : ℝ) * (49 / 5 : ℝ) * t ^ 2 =
          signedLengthInMeters
            (setup.verticalDisplacement setup.landingTime) := by
        rw [_laws.verticalConstantGravityMotion]
        simp only [v, s, t]
        rw [_gravity.gravityMetersPerSecondSquared]
      _ = lengthInMeters setup.roofHeight := _laws.landsAtRoofHeight
      _ = 6 := _description.roofHeightMeters
  rw [hvs] at hyWall hyLanding

  have hproduct :
      0 <
        (t - 11 / 5) *
          ((49 / 10 : ℝ) * (t + 11 / 5) - w) := by
    nlinarith [hyWall, hyLanding]
  have hafterVertex :
      0 < (49 / 5 : ℝ) * t - w := by
    have hfactor :
        0 < (49 / 10 : ℝ) * (t + 11 / 5) - w := by
      rcases mul_pos_iff.mp hproduct with hpositive | hnegative
      · exact hpositive.2
      · exfalso
        linarith
    nlinarith
  have hsquare :
      ((49 / 5 : ℝ) * t - w) ^ 2 =
        w ^ 2 - 2 * (49 / 5 : ℝ) * 6 := by
    nlinarith [hyLanding]
  have hsqrt :
      Real.sqrt (w ^ 2 - 2 * (49 / 5 : ℝ) * 6) =
        (49 / 5 : ℝ) * t - w := by
    calc
      Real.sqrt (w ^ 2 - 2 * (49 / 5 : ℝ) * 6) =
          Real.sqrt (((49 / 5 : ℝ) * t - w) ^ 2) := by
            rw [hsquare]
      _ = |(49 / 5 : ℝ) * t - w| := Real.sqrt_sq_eq_abs _
      _ = (49 / 5 : ℝ) * t - w := abs_of_pos hafterVertex
  have htFormula :
      t =
        (w + Real.sqrt (w ^ 2 - 2 * (49 / 5 : ℝ) * 6)) /
          (49 / 5 : ℝ) := by
    rw [hsqrt]
    ring

  have hdistance :
      lengthInMeters setup.landingDistanceFromWall =
        (120 / 11 : ℝ) * (t - 11 / 5) := by
    have hxLanding :
        (120 / 11 : ℝ) * t =
          24 + lengthInMeters setup.landingDistanceFromWall := by
      calc
        (120 / 11 : ℝ) * t = v * c * t := by rw [hvc]
        _ =
            signedLengthInMeters
              (setup.horizontalDisplacement setup.landingTime) := by
          rw [_laws.uniformHorizontalMotion]
        _ =
            lengthInMeters setup.launchToWallDistance +
              lengthInMeters setup.landingDistanceFromWall :=
          _laws.landingDistanceIsMeasuredFromWall
        _ = 24 + lengthInMeters setup.landingDistanceFromWall := by
          rw [_description.launchToWallDistanceMeters]
    nlinarith
  have htComputed : computedLandingTimeInSeconds = t := by
    norm_num [computedLandingTimeInSeconds, w, s, c,
      _description.launchAngleDegrees] at ⊢ htFormula
    exact htFormula.symm
  rw [computedLandingDistanceInMeters, htComputed]
  norm_num
  norm_num at hdistance
  exact hdistance

/-!
The computed distance is approximately `2.7912 m`; hence the physical landing
distance agrees with `2.79 m` to the displayed centimetre and choice C is the
unique closest printed choice.

Blueprint: `thm:physics:phyx_mini_0685:target`.
-/
theorem problem_phyx_mini_0685
    (setup : RooftopProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesIdealProjectileLaws setup) :
    lengthInMeters setup.landingDistanceFromWall =
        computedLandingDistanceInMeters ∧
      MatchesDisplayedDistance setup.landingDistanceFromWall .C ∧
      IsUniqueClosestDisplayedDistance setup.landingDistanceFromWall .C :=
    set_option maxHeartbeats 2000000 in by
  have hExactDistance :=
    landingDistance_eq_computedExpression setup _description _gravity
      _physical _laws
  have hDGap :
      (1 : ℝ) / 200 + 213 / 100 < 2.785 := by norm_num

  /-
  The imported trigonometric Taylor bounds are accurate at small arguments.
  This helper propagates a rational enclosure through one angle doubling.
  -/
  have nextUpperBounds {x su cu su' cu' : ℝ}
      (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
      (hs : Real.sin x < su) (hc : Real.cos x < cu)
      (hsUpper : 2 * su * cu ≤ su')
      (hcUpper : 2 * cu ^ 2 - 1 ≤ cu') :
      Real.sin (2 * x) < su' ∧ Real.cos (2 * x) < cu' := by
    have hsin : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0
        (hx1.trans (by linarith [Real.two_le_pi]))
    have hcos : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by nlinarith [Real.pi_pos], hx1.trans Real.one_le_pi_div_two⟩
    rw [Real.sin_two_mul, Real.cos_two_mul]
    constructor
    · calc
        2 * Real.sin x * Real.cos x ≤ 2 * su * Real.cos x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs.le (by norm_num)) hcos
        _ < 2 * su * cu :=
          mul_lt_mul_of_pos_left hc
            (mul_pos (by norm_num) (lt_of_le_of_lt hsin hs))
        _ ≤ su' := hsUpper
    · nlinarith [hcUpper,
        mul_nonneg (sub_nonneg.mpr hc.le)
          (add_nonneg (lt_of_le_of_lt hcos hc).le hcos)]
  have nextLowerBounds {x sl cl sl' cl' : ℝ}
      (hsl : 0 < sl) (hcl : 0 < cl)
      (hs : sl < Real.sin x) (hc : cl < Real.cos x)
      (hsLower : sl' ≤ 2 * sl * cl)
      (hcLower : cl' ≤ 2 * cl ^ 2 - 1) :
      sl' < Real.sin (2 * x) ∧ cl' < Real.cos (2 * x) := by
    have hsin : 0 < Real.sin x := lt_trans hsl hs
    have hcos : 0 < Real.cos x := lt_trans hcl hc
    rw [Real.sin_two_mul, Real.cos_two_mul]
    constructor
    · calc
        sl' ≤ 2 * sl * cl := hsLower
        _ < 2 * Real.sin x * cl :=
          mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_left hs (by norm_num)) hcl
        _ < 2 * Real.sin x * Real.cos x :=
          mul_lt_mul_of_pos_left hc (mul_pos (by norm_num) hsin)
    · nlinarith [hcLower,
        mul_pos (sub_pos.mpr hc) (add_pos hcos hcl)]

  /-
  Certify `3.1415 < pi < 3.14166`.  At one 64th of a sixth
  turn, the fourth-order Taylor remainder is small enough; six exact
  double-angle steps then distinguish the endpoint sine from `1 / 2`.
  -/
  have hPiL0 :
      Real.sin ((3.1415 : ℝ) / 384) < (0.00818090 : ℝ) ∧
        Real.cos ((3.1415 : ℝ) / 384) < (0.99996654 : ℝ) := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (3.1415 : ℝ) / 384) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (3.1415 : ℝ) / 384) (by norm_num))
    norm_num [abs_of_nonneg] at hs hc ⊢
    constructor
    · nlinarith [hs.2]
    · nlinarith [hc.2]
  have hPiL1 := nextUpperBounds
    (su' := (0.01636126 : ℝ)) (cu' := 0.99986617)
    (by norm_num) (by norm_num) hPiL0.1 hPiL0.2
    (by norm_num) (by norm_num)
  have hPiL2 := nextUpperBounds
    (su' := (0.03271815 : ℝ)) (cu' := 0.99946472)
    (by norm_num) (by norm_num) hPiL1.1 hPiL1.2
    (by norm_num) (by norm_num)
  have hPiL3 := nextUpperBounds
    (su' := (0.06540128 : ℝ)) (cu' := 0.99785946)
    (by norm_num) (by norm_num) hPiL2.1 hPiL2.2
    (by norm_num) (by norm_num)
  have hPiL4 := nextUpperBounds
    (su' := (0.13052258 : ℝ)) (cu' := 0.99144701)
    (by norm_num) (by norm_num) hPiL3.1 hPiL3.2
    (by norm_num) (by norm_num)
  have hPiL5 := nextUpperBounds
    (su' := (0.25881245 : ℝ)) (cu' := 0.96593435)
    (by norm_num) (by norm_num) hPiL4.1 hPiL4.2
    (by norm_num) (by norm_num)
  have hPiL6 := nextUpperBounds
    (su' := (0.49999168 : ℝ)) (cu' := 0.86605834)
    (by norm_num) (by norm_num) hPiL5.1 hPiL5.2
    (by norm_num) (by norm_num)

  have hPiU0 :
      (0.00818131 : ℝ) < Real.sin ((3.14166 : ℝ) / 384) ∧
        (0.99996653 : ℝ) < Real.cos ((3.14166 : ℝ) / 384) := by
    have hs := abs_le.mp
      (Real.sin_bound (x := (3.14166 : ℝ) / 384) (by norm_num))
    have hc := abs_le.mp
      (Real.cos_bound (x := (3.14166 : ℝ) / 384) (by norm_num))
    norm_num [abs_of_nonneg] at hs hc ⊢
    constructor
    · nlinarith [hs.1]
    · nlinarith [hc.1]
  have hPiU1 := nextLowerBounds
    (sl' := (0.01636207 : ℝ)) (cl' := 0.99986612)
    (by norm_num) (by norm_num) hPiU0.1 hPiU0.2
    (by norm_num) (by norm_num)
  have hPiU2 := nextLowerBounds
    (sl' := (0.03271975 : ℝ)) (cl' := 0.99946451)
    (by norm_num) (by norm_num) hPiU1.1 hPiU1.2
    (by norm_num) (by norm_num)
  have hPiU3 := nextLowerBounds
    (sl' := (0.06540445 : ℝ)) (cl' := 0.99785861)
    (by norm_num) (by norm_num) hPiU2.1 hPiU2.2
    (by norm_num) (by norm_num)
  have hPiU4 := nextLowerBounds
    (sl' := (0.13052878 : ℝ)) (cl' := 0.99144361)
    (by norm_num) (by norm_num) hPiU3.1 hPiU3.2
    (by norm_num) (by norm_num)
  have hPiU5 := nextLowerBounds
    (sl' := (0.25882384 : ℝ)) (cl' := 0.96592086)
    (by norm_num) (by norm_num) hPiU4.1 hPiU4.2
    (by norm_num) (by norm_num)
  have hPiU6 := nextLowerBounds
    (sl' := (0.50000669 : ℝ)) (cl' := 0.86600621)
    (by norm_num) (by norm_num) hPiU5.1 hPiU5.2
    (by norm_num) (by norm_num)

  clear hPiL0 hPiL1 hPiL2 hPiL3 hPiL4 hPiL5
    hPiU0 hPiU1 hPiU2 hPiU3 hPiU4 hPiU5
    nextUpperBounds nextLowerBounds
  have hsqrtTwo :
      (1.41421356 : ℝ) < Real.sqrt 2 ∧
        Real.sqrt 2 < (1.41421357 : ℝ) := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    set_option maxHeartbeats 800000 in
      constructor <;> nlinarith
  have hPiBounds :
      (3.1415 : ℝ) < Real.pi ∧ Real.pi < (3.14166 : ℝ) := by
    norm_num at hPiL6 hPiU6
    have hLowerSine :
        Real.sin ((3.1415 : ℝ) / 6) <
          Real.sin (Real.pi / 6) := by
      rw [Real.sin_pi_div_six]
      linarith [hPiL6.1]
    have hUpperSine :
        Real.sin (Real.pi / 6) <
          Real.sin ((3.14166 : ℝ) / 6) := by
      rw [Real.sin_pi_div_six]
      linarith [hPiU6.1]
    have hLowerMem :
        (3.1415 : ℝ) / 6 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.two_le_pi]
    have hPiMem :
        Real.pi / 6 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hUpperMem :
        (3.14166 : ℝ) / 6 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.two_le_pi]
    constructor
    · have :=
        (Real.strictMonoOn_sin.lt_iff_lt hLowerMem hPiMem).mp hLowerSine
      linarith
    · have :=
        (Real.strictMonoOn_sin.lt_iff_lt hPiMem hUpperMem).mp hUpperSine
      linarith

  clear hPiL6 hPiU6
  let delta : ℝ := 2 * Real.pi / 45
  have hdelta :
      (0.1396199 : ℝ) < delta ∧ delta < (0.1396294 : ℝ) := by
    dsimp [delta]
    constructor <;> nlinarith [hPiBounds.1, hPiBounds.2]
  have hdeltaPos : 0 < delta := lt_trans (by norm_num) hdelta.1
  have hdeltaSq :
      (0.0194937 : ℝ) < delta ^ 2 ∧
        delta ^ 2 < (0.0194964 : ℝ) := by
    constructor
    · nlinarith [mul_pos (sub_pos.mpr hdelta.1)
        (add_pos hdeltaPos
          (by norm_num : 0 < (0.1396199 : ℝ)))]
    · nlinarith [mul_pos (sub_pos.mpr hdelta.2)
        (add_pos (by norm_num : 0 < (0.1396294 : ℝ))
          hdeltaPos)]
  have hdeltaCube :
      (0.0027217 : ℝ) < delta ^ 3 ∧
        delta ^ 3 < (0.0027223 : ℝ) := by
    constructor
    · calc
        (0.0027217 : ℝ) <
            (0.1396199 : ℝ) * (0.0194937 : ℝ) := by norm_num
        _ < delta * (0.0194937 : ℝ) :=
          mul_lt_mul_of_pos_right hdelta.1 (by norm_num)
        _ < delta * delta ^ 2 :=
          mul_lt_mul_of_pos_left hdeltaSq.1 hdeltaPos
        _ = delta ^ 3 := by ring
    · calc
        delta ^ 3 = delta * delta ^ 2 := by ring
        _ < (0.1396294 : ℝ) * delta ^ 2 :=
          mul_lt_mul_of_pos_right hdelta.2 (sq_pos_of_pos hdeltaPos)
        _ < (0.1396294 : ℝ) * (0.0194964 : ℝ) :=
          mul_lt_mul_of_pos_left hdeltaSq.2 (by norm_num)
        _ < (0.0027223 : ℝ) := by norm_num
  have hdeltaFourth :
      delta ^ 4 < (0.0003802 : ℝ) := by
    calc
      delta ^ 4 = delta ^ 2 * delta ^ 2 := by ring
      _ < (0.0194964 : ℝ) * delta ^ 2 :=
        mul_lt_mul_of_pos_right hdeltaSq.2 (sq_pos_of_pos hdeltaPos)
      _ < (0.0194964 : ℝ) * (0.0194964 : ℝ) :=
        mul_lt_mul_of_pos_left hdeltaSq.2 (by norm_num)
      _ < (0.0003802 : ℝ) := by norm_num
  have hdeltaAbs : |delta| ≤ (1 : ℝ) := by
    rw [abs_of_pos hdeltaPos]
    exact hdelta.2.le.trans (by norm_num)
  have hsinDeltaRaw :=
    abs_le.mp (Real.sin_bound (x := delta) hdeltaAbs)
  have hcosDeltaRaw :=
    abs_le.mp (Real.cos_bound (x := delta) hdeltaAbs)
  rw [abs_of_pos hdeltaPos] at hsinDeltaRaw hcosDeltaRaw
  have hsinDelta :
      (0.1391463 : ℝ) < Real.sin delta ∧
        Real.sin delta < (0.1391956 : ℝ) := by
    constructor <;>
      linarith only [hsinDeltaRaw.1, hsinDeltaRaw.2, hdelta.1,
        hdelta.2, hdeltaCube.1, hdeltaCube.2, hdeltaFourth]
  have hcosDelta :
      (0.9902319 : ℝ) < Real.cos delta ∧
        Real.cos delta < (0.9902730 : ℝ) := by
    have hTaylorLower :
        1 - delta ^ 2 / 2 - delta ^ 4 * (5 / 96 : ℝ) ≤
          Real.cos delta := by
      have h :
          (1 - delta ^ 2 / 2) + -(delta ^ 4 * (5 / 96 : ℝ)) ≤
            (1 - delta ^ 2 / 2) +
              (Real.cos delta - (1 - delta ^ 2 / 2)) :=
        add_le_add_right hcosDeltaRaw.1 (1 - delta ^ 2 / 2)
      calc
        1 - delta ^ 2 / 2 - delta ^ 4 * (5 / 96 : ℝ) =
            (1 - delta ^ 2 / 2) +
              -(delta ^ 4 * (5 / 96 : ℝ)) := rfl
        _ ≤ (1 - delta ^ 2 / 2) +
              (Real.cos delta - (1 - delta ^ 2 / 2)) := h
        _ = Real.cos delta := by
          rw [← add_sub_assoc, add_sub_cancel_left]
    have hTaylorUpper :
      Real.cos delta ≤
          1 - delta ^ 2 / 2 + delta ^ 4 * (5 / 96 : ℝ) := by
      have h :
          (1 - delta ^ 2 / 2) +
              (Real.cos delta - (1 - delta ^ 2 / 2)) ≤
            (1 - delta ^ 2 / 2) + delta ^ 4 * (5 / 96 : ℝ) :=
        add_le_add_right hcosDeltaRaw.2 (1 - delta ^ 2 / 2)
      calc
        Real.cos delta =
            (1 - delta ^ 2 / 2) +
              (Real.cos delta - (1 - delta ^ 2 / 2)) := by
                rw [← add_sub_assoc, add_sub_cancel_left]
        _ ≤ (1 - delta ^ 2 / 2) +
              delta ^ 4 * (5 / 96 : ℝ) := h
        _ = 1 - delta ^ 2 / 2 +
              delta ^ 4 * (5 / 96 : ℝ) := rfl
    constructor
    · calc
        (0.9902319 : ℝ) <
            1 - (0.0194964 : ℝ) / 2 -
              (0.0003802 : ℝ) * (5 / 96 : ℝ) := by norm_num
        _ < 1 - delta ^ 2 / 2 -
              delta ^ 4 * (5 / 96 : ℝ) := by
          linarith only [hdeltaSq.2, hdeltaFourth]
        _ ≤ Real.cos delta := hTaylorLower
    · calc
        Real.cos delta ≤
            1 - delta ^ 2 / 2 +
              delta ^ 4 * (5 / 96 : ℝ) := hTaylorUpper
        _ < 1 - (0.0194937 : ℝ) / 2 +
              (0.0003802 : ℝ) * (5 / 96 : ℝ) := by
          linarith only [hdeltaSq.1, hdeltaFourth]
        _ < (0.9902730 : ℝ) := by norm_num
  have hhalfSqrtTwo :
      (0.70710678 : ℝ) < Real.sqrt 2 / 2 ∧
        Real.sqrt 2 / 2 < (0.707106785 : ℝ) := by
    constructor <;> linarith only [hsqrtTwo.1, hsqrtTwo.2]
  have hsum :
      (1.129378 : ℝ) < Real.cos delta + Real.sin delta ∧
        Real.cos delta + Real.sin delta < (1.1294687 : ℝ) := by
    constructor <;> linarith [hsinDelta.1, hsinDelta.2,
      hcosDelta.1, hcosDelta.2]
  have hdifference :
      (0.8510363 : ℝ) < Real.cos delta - Real.sin delta ∧
        Real.cos delta - Real.sin delta < (0.8511268 : ℝ) := by
    constructor <;> linarith [hsinDelta.1, hsinDelta.2,
      hcosDelta.1, hcosDelta.2]
  have hsinProduct :
      (0.7985908 : ℝ) <
          Real.sqrt 2 / 2 * (Real.cos delta + Real.sin delta) ∧
        Real.sqrt 2 / 2 * (Real.cos delta + Real.sin delta) <
          (0.7986550 : ℝ) := by
    constructor
    · calc
        (0.7985908 : ℝ) <
            (0.70710678 : ℝ) * (1.129378 : ℝ) := by norm_num
        _ < Real.sqrt 2 / 2 * (1.129378 : ℝ) :=
          mul_lt_mul_of_pos_right hhalfSqrtTwo.1 (by norm_num)
        _ < Real.sqrt 2 / 2 *
            (Real.cos delta + Real.sin delta) :=
          mul_lt_mul_of_pos_left hsum.1
            (lt_trans (by norm_num) hhalfSqrtTwo.1)
    · calc
        Real.sqrt 2 / 2 * (Real.cos delta + Real.sin delta) <
            (0.707106785 : ℝ) *
              (Real.cos delta + Real.sin delta) :=
          mul_lt_mul_of_pos_right hhalfSqrtTwo.2
            (lt_trans (by norm_num) hsum.1)
        _ < (0.707106785 : ℝ) * (1.1294687 : ℝ) :=
          mul_lt_mul_of_pos_left hsum.2 (by norm_num)
        _ < (0.7986550 : ℝ) := by norm_num
  have hcosProduct :
      (0.6017735 : ℝ) <
          Real.sqrt 2 / 2 * (Real.cos delta - Real.sin delta) ∧
        Real.sqrt 2 / 2 * (Real.cos delta - Real.sin delta) <
          (0.6018376 : ℝ) := by
    constructor
    · calc
        (0.6017735 : ℝ) <
            (0.70710678 : ℝ) * (0.8510363 : ℝ) := by norm_num
        _ < Real.sqrt 2 / 2 * (0.8510363 : ℝ) :=
          mul_lt_mul_of_pos_right hhalfSqrtTwo.1 (by norm_num)
        _ < Real.sqrt 2 / 2 *
            (Real.cos delta - Real.sin delta) :=
          mul_lt_mul_of_pos_left hdifference.1
            (lt_trans (by norm_num) hhalfSqrtTwo.1)
    · calc
        Real.sqrt 2 / 2 * (Real.cos delta - Real.sin delta) <
            (0.707106785 : ℝ) *
              (Real.cos delta - Real.sin delta) :=
          mul_lt_mul_of_pos_right hhalfSqrtTwo.2
            (lt_trans (by norm_num) hdifference.1)
        _ < (0.707106785 : ℝ) * (0.8511268 : ℝ) :=
          mul_lt_mul_of_pos_left hdifference.2 (by norm_num)
        _ < (0.6018376 : ℝ) := by norm_num

  have hangle :
      (53 : ℝ) * Real.pi / 180 = Real.pi / 4 + delta := by
    dsimp [delta]
    ring
  have hsinTheta :
      (0.7985908 : ℝ) < Real.Angle.sin (degrees 53) ∧
        Real.Angle.sin (degrees 53) < (0.7986550 : ℝ) := by
    change
      (0.7985908 : ℝ) < Real.sin ((53 : ℝ) * Real.pi / 180) ∧
        Real.sin ((53 : ℝ) * Real.pi / 180) < (0.7986550 : ℝ)
    rw [hangle, Real.sin_add, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    simpa only [mul_add] using hsinProduct
  have hcosTheta :
      (0.6017735 : ℝ) < Real.Angle.cos (degrees 53) ∧
        Real.Angle.cos (degrees 53) < (0.6018376 : ℝ) := by
    change
      (0.6017735 : ℝ) < Real.cos ((53 : ℝ) * Real.pi / 180) ∧
        Real.cos ((53 : ℝ) * Real.pi / 180) < (0.6018376 : ℝ)
    rw [hangle, Real.cos_add, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    simpa only [mul_sub] using hcosProduct

  let verticalSpeed : ℝ :=
    (120 / 11 : ℝ) * Real.Angle.sin (degrees 53) /
      Real.Angle.cos (degrees 53)
  have hverticalSpeed :
      (14.4754 : ℝ) < verticalSpeed ∧
        verticalSpeed < (14.47821 : ℝ) := by
    have hcpos : 0 < Real.Angle.cos (degrees 53) :=
      lt_trans (by norm_num) hcosTheta.1
    dsimp [verticalSpeed]
    constructor
    · apply (lt_div_iff₀ hcpos).2
      linarith only [hsinTheta.1, hcosTheta.2]
    · apply (div_lt_iff₀ hcpos).2
      linarith only [hsinTheta.2, hcosTheta.1]
  have hverticalSpeedSq :
      (14.4754 : ℝ) ^ 2 < verticalSpeed ^ 2 ∧
        verticalSpeed ^ 2 < (14.47821 : ℝ) ^ 2 := by
    constructor
    · exact (sq_lt_sq₀ (by norm_num)
        (lt_trans (by norm_num) hverticalSpeed.1).le).2
          hverticalSpeed.1
    · exact (sq_lt_sq₀
        (lt_trans (by norm_num) hverticalSpeed.1).le
        (by norm_num)).2 hverticalSpeed.2
  have hdiscriminant :
      (0 : ℝ) ≤ verticalSpeed ^ 2 - 2 * (49 / 5 : ℝ) * 6 := by
    linarith only [hverticalSpeedSq.1]
  have hsqrtDiscriminant :
      (9.5883 : ℝ) <
          Real.sqrt
            (verticalSpeed ^ 2 - 2 * (49 / 5 : ℝ) * 6) ∧
        Real.sqrt
            (verticalSpeed ^ 2 - 2 * (49 / 5 : ℝ) * 6) <
          (9.592631 : ℝ) := by
    constructor
    · apply (Real.lt_sqrt (by norm_num)).2
      linarith only [hverticalSpeedSq.1]
    · apply (Real.sqrt_lt hdiscriminant (by norm_num)).2
      linarith only [hverticalSpeedSq.2]
  have hcomputedFormula :
      computedLandingDistanceInMeters =
        (120 / 11 : ℝ) *
          ((verticalSpeed +
              Real.sqrt
                (verticalSpeed ^ 2 - 2 * (49 / 5 : ℝ) * 6)) /
              (49 / 5 : ℝ) -
            11 / 5) := by
    norm_num [computedLandingDistanceInMeters,
      computedLandingTimeInSeconds, verticalSpeed]
  have hcomputed :
      (2.785 : ℝ) < computedLandingDistanceInMeters ∧
        computedLandingDistanceInMeters < (2.795 : ℝ) := by
    rw [hcomputedFormula]
    constructor <;> linarith only [hverticalSpeed.1,
      hverticalSpeed.2, hsqrtDiscriminant.1, hsqrtDiscriminant.2]

  clear hsqrtTwo hPiBounds delta hdelta hdeltaPos hdeltaSq hdeltaCube
    hdeltaFourth hdeltaAbs hsinDeltaRaw hcosDeltaRaw hsinDelta
    hcosDelta hhalfSqrtTwo hsum hdifference hsinProduct hcosProduct
    hangle hsinTheta hcosTheta verticalSpeed hverticalSpeed
    hverticalSpeedSq hdiscriminant hsqrtDiscriminant hcomputedFormula
  let x : ℝ := lengthInMeters setup.landingDistanceFromWall
  have hx : (2.785 : ℝ) < x ∧ x < (2.795 : ℝ) := by
    simpa [x, hExactDistance] using hcomputed
  have hCabs : |x - 279 / 100| ≤ (1 : ℝ) / 200 := by
    rw [abs_le]
    constructor <;> linarith only [hx.1, hx.2]
  have hAabs : |x - 286 / 100| = 286 / 100 - x := by
    rw [abs_of_nonpos (by linarith only [hx.2]), neg_sub]
  have hBabs : |x - 312 / 100| = 312 / 100 - x := by
    rw [abs_of_nonpos (by linarith only [hx.2]), neg_sub]
  have hDabs : |x - 213 / 100| = x - 213 / 100 := by
    rw [abs_of_nonneg (by linarith only [hx.1])]
  have hCltA : |x - 279 / 100| < |x - 286 / 100| := by
    rw [hAabs]
    linarith only [hCabs, hx.2]
  have hCltB : |x - 279 / 100| < |x - 312 / 100| := by
    rw [hBabs]
    linarith only [hCabs, hx.2]
  have hCltD : |x - 279 / 100| < |x - 213 / 100| := by
    rw [hDabs]
    apply hCabs.trans_lt
    apply (lt_sub_iff_add_lt).2
    exact hDGap.trans hx.1

  refine ⟨hExactDistance, ?_, ?_⟩
  · change |x - 279 / 100| ≤ (1 : ℝ) / 200
    exact hCabs
  · constructor
    · intro other
      fin_cases other
      · change |x - 279 / 100| ≤ |x - 286 / 100|
        exact hCltA.le
      · change |x - 279 / 100| ≤ |x - 312 / 100|
        exact hCltB.le
      · exact le_rfl
      · change |x - 279 / 100| ≤ |x - 213 / 100|
        exact hCltD.le
    · intro other hother
      fin_cases other
      · have hcontra := hother .C
        change |x - 286 / 100| ≤ |x - 279 / 100| at hcontra
        exact (not_le_of_gt hCltA hcontra).elim
      · have hcontra := hother .C
        change |x - 312 / 100| ≤ |x - 279 / 100| at hcontra
        exact (not_le_of_gt hCltB hcontra).elim
      · rfl
      · have hcontra := hother .C
        change |x - 213 / 100| ≤ |x - 279 / 100| at hcontra
        exact (not_le_of_gt hCltD hcontra).elim

end PhyXMiniProblems.ProblemPhyXMini0685
