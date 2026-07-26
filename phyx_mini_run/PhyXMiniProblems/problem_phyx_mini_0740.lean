import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0740

open Dimension

/-!
# A ball thrown toward a vertical wall

A ball is released with speed `25.0 m/s` at `40.0 degrees` above the
horizontal.  A vertical wall is `22.0 m` horizontally from the release point.
Under the usual no-drag, uniform-gravity projectile model, the question asks
for the ball's height above its release point when it hits the wall.

Physical lengths, times, speeds, and accelerations use Physlib's
unit-independent `Dimensionful (WithDim ...)` quantities.  Real numbers occur
only as coherent-SI readouts, dimensionless drawing coordinates, trigonometric
values, and displayed multiple-choice values.

Assumption/target split:

* `MatchesPrimaryFigure` records the thrower, ball, dotted path, angle arc,
  horizontal distance arrow, ground, and vertical brick wall shown in the
  raster;
* `MatchesProblemDescription` records `25.0 m/s`, `40.0 degrees`, and `22.0 m`;
* `UsesStandardNearEarthGravity` supplies the textbook `9.8 m/s^2`
  calibration;
* `SatisfiesIdealProjectileKinematics` and `DescribesWallImpact` state the
  governing motion and impact-incidence relations; and
* only the derived lemmas and `problem_phyx_mini_0740` identify the independent
  impact-height observable with the projectile prediction or select choice C.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Acceleration has physical dimension `L T^-2`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical displacement along one Cartesian axis. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent elapsed duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed displacement in metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical duration in seconds. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a physical speed magnitude in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image vocabulary -/

/-- The idealization used for the flight between release and wall impact. -/
inductive ProjectileModel where
  | uniformGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- Literal objects visibly represented in image `740.png`. -/
inductive FigureObject where
  | thrower
  | ball
  | brickWall
  | ground
  deriving DecidableEq, Fintype, Repr

/-- Mathematical labels visibly printed in the primary image. -/
inductive FigureLabel where
  | launchAngleThetaZero
  | horizontalDistanceD
  deriving DecidableEq, Fintype, Repr

/-- Schematic anchors used to retain the spatial relations in the raster. -/
inductive FigureAnchor where
  | releasePoint
  | shownBall
  | wallBase
  | wallTop
  | distanceArrowLeft
  | distanceArrowRight
  deriving DecidableEq, Fintype, Repr

/-!
The primary-image transcription.  Its real coordinates are dimensionless
drawing coordinates rather than physical measurements.  The two labelled
physical quantities remain dimensionful and are connected to the experiment
by `MatchesPrimaryFigure`.
-/
structure BallWallFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  horizontalCoordinate : FigureAnchor → ℝ
  verticalCoordinate : FigureAnchor → ℝ
  labelledHorizontalDistance : LengthQuantity
  labelledLaunchAngle : Real.Angle
  dottedTrajectoryShown : Bool
  launchDirectionSegmentShown : Bool
  launchAngleArcShown : Bool
  horizontalDoubleArrowShown : Bool
  wallBrickPatternShown : Bool
  groundPatternShown : Bool

/-!
Independent physical observables of the experiment.  The coordinate functions
give displacement from the release point as a function of physical elapsed
time.  In particular, `impactHeightAboveRelease` and `impactTime` are not
defined from the requested answer or from an eliminated projectile formula.
-/
structure BallWallProjectileSetup where
  model : ProjectileModel
  initialSpeed : SpeedQuantity
  launchAngle : Real.Angle
  wallHorizontalDistance : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  impactTime : TimeQuantity
  impactHeightAboveRelease : LengthQuantity
  horizontalDisplacement : TimeQuantity → SignedLengthQuantity
  verticalDisplacement : TimeQuantity → SignedLengthQuantity
  figure : BallWallFigure

/-! ## Figure evidence, source data, and governing laws -/

/-!
The raster shows the release point to the left of the vertical wall, a ball
above and to the right of release but still left of the wall, the horizontal
arrow labelled `d`, and the angle `theta_0` above a horizontal reference.
The image itself does not display a numerical impact height.
-/
structure MatchesPrimaryFigure (setup : BallWallProjectileSetup) : Prop where
  everyNamedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyNamedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  distanceLabelMatchesSetup :
    setup.figure.labelledHorizontalDistance = setup.wallHorizontalDistance
  angleLabelMatchesSetup :
    setup.figure.labelledLaunchAngle = setup.launchAngle
  releasePointIsLeftOfWall :
    setup.figure.horizontalCoordinate .releasePoint <
      setup.figure.horizontalCoordinate .wallBase
  wallIsVertical :
    setup.figure.horizontalCoordinate .wallBase =
      setup.figure.horizontalCoordinate .wallTop
  wallRisesAboveItsBase :
    setup.figure.verticalCoordinate .wallBase <
      setup.figure.verticalCoordinate .wallTop
  shownBallIsRightOfRelease :
    setup.figure.horizontalCoordinate .releasePoint <
      setup.figure.horizontalCoordinate .shownBall
  shownBallIsLeftOfWall :
    setup.figure.horizontalCoordinate .shownBall <
      setup.figure.horizontalCoordinate .wallBase
  shownBallIsAboveRelease :
    setup.figure.verticalCoordinate .releasePoint <
      setup.figure.verticalCoordinate .shownBall
  distanceArrowIsHorizontal :
    setup.figure.verticalCoordinate .distanceArrowLeft =
      setup.figure.verticalCoordinate .distanceArrowRight
  distanceArrowRunsFromReleaseToWall :
    setup.figure.horizontalCoordinate .distanceArrowLeft =
        setup.figure.horizontalCoordinate .releasePoint ∧
      setup.figure.horizontalCoordinate .distanceArrowRight =
        setup.figure.horizontalCoordinate .wallBase
  dottedPathShown : setup.figure.dottedTrajectoryShown = true
  launchSegmentShown : setup.figure.launchDirectionSegmentShown = true
  angleArcShown : setup.figure.launchAngleArcShown = true
  horizontalDistanceArrowShown :
    setup.figure.horizontalDoubleArrowShown = true
  brickPatternShown : setup.figure.wallBrickPatternShown = true
  texturedGroundShown : setup.figure.groundPatternShown = true

/-- Convert a degree readout to a physical angle modulo `2 * pi`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-!
Numerical and qualitative data stated in the problem prose.  No field here
mentions the impact height or an answer choice.
-/
structure MatchesProblemDescription
    (setup : BallWallProjectileSetup) : Prop where
  idealProjectileModel :
    setup.model = .uniformGravityNegligibleDrag
  initialSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 25
  launchAngleDegrees : setup.launchAngle = degrees 40
  wallDistanceMeters :
    lengthInMeters setup.wallHorizontalDistance = 22

/-!
The standard near-Earth gravitational calibration implicit in the textbook
answer.  It is independent of the requested impact height.
-/
structure UsesStandardNearEarthGravity
    (setup : BallWallProjectileSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
Strict positivity and the up-and-right launch branch shown by the figure.
These assumptions support cancellation of horizontal speed and exclude a
spurious backwards or zero-time incidence.
-/
structure HasPhysicalProjectileParameters
    (setup : BallWallProjectileSetup) : Prop where
  wallDistancePositive :
    0 < lengthInMeters setup.wallHorizontalDistance
  initialSpeedPositive :
    0 < speedInMetersPerSecond setup.initialSpeed
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  impactTimePositive : 0 < timeInSeconds setup.impactTime
  launchPointsRight : 0 < Real.Angle.cos setup.launchAngle
  launchPointsUp : 0 < Real.Angle.sin setup.launchAngle

/-!
Ideal no-drag projectile motion in coherent SI component readouts.  Horizontal
velocity is constant; vertical acceleration is the uniform downward `g`.
The two equations are governing laws for every elapsed duration and contain no
wall-impact height formula or answer-choice value.
-/
structure SatisfiesIdealProjectileKinematics
    (setup : BallWallProjectileSetup) : Prop where
  uniformHorizontalMotion : ∀ duration : TimeQuantity,
    signedLengthInMeters (setup.horizontalDisplacement duration) =
      speedInMetersPerSecond setup.initialSpeed *
        Real.Angle.cos setup.launchAngle * timeInSeconds duration
  verticalConstantGravityMotion : ∀ duration : TimeQuantity,
    signedLengthInMeters (setup.verticalDisplacement duration) =
      speedInMetersPerSecond setup.initialSpeed *
          Real.Angle.sin setup.launchAngle * timeInSeconds duration -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          timeInSeconds duration ^ 2

/-!
Incidence and measurement relations for the independently stored wall-impact
event.  They only say that the impact lies at the wall and that the named
height is its vertical displacement above release.
-/
structure DescribesWallImpact (setup : BallWallProjectileSetup) : Prop where
  impactIsAtWallHorizontalCoordinate :
    signedLengthInMeters
        (setup.horizontalDisplacement setup.impactTime) =
      lengthInMeters setup.wallHorizontalDistance
  impactHeightIsVerticalDisplacement :
    signedLengthInMeters
        (setup.verticalDisplacement setup.impactTime) =
      lengthInMeters setup.impactHeightAboveRelease

/-! ## Derived prediction and displayed answers -/

/-- The wall-arrival time predicted by uniform horizontal motion. -/
noncomputable def predictedImpactTimeInSeconds
    (setup : BallWallProjectileSetup) : ℝ :=
  lengthInMeters setup.wallHorizontalDistance /
    (speedInMetersPerSecond setup.initialSpeed *
      Real.Angle.cos setup.launchAngle)

/-!
The height above release predicted after substituting the derived wall-arrival
time into the vertical projectile equation.  This expression does not define
the independent physical impact-height field.
-/
noncomputable def predictedImpactHeightInMeters
    (setup : BallWallProjectileSetup) : ℝ :=
  speedInMetersPerSecond setup.initialSpeed *
      Real.Angle.sin setup.launchAngle *
      predictedImpactTimeInSeconds setup -
    (1 / 2 : ℝ) *
      accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration *
      predictedImpactTimeInSeconds setup ^ 2

/-!
The exact real expression obtained from the displayed `25`, `40 degrees`,
`22`, and the conventional `9.8` calibration.  Its numerical value is about
`12.0`, but it is not definitionally set equal to `12`.
-/
noncomputable def computedImpactHeightInMeters : ℝ :=
  let angle : Real.Angle := degrees 40
  let impactTime : ℝ := 22 / (25 * Real.Angle.cos angle)
  25 * Real.Angle.sin angle * impactTime -
    (1 / 2 : ℝ) * (49 / 5 : ℝ) * impactTime ^ 2

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Height in metres printed beside each displayed answer label. -/
def AnswerChoice.displayedHeightInMeters : AnswerChoice → ℝ
  | .A => 8
  | .B => 10
  | .C => 12
  | .D => 14

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a displayed whole-metre height to within half a metre. -/
def MatchesDisplayedHeight
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters height - choice.displayedHeightInMeters| < (1 / 2 : ℝ)

/-- A choice is strictly closer to the physical height than every alternative. -/
def IsUniqueClosestDisplayedHeight
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters height - choice.displayedHeightInMeters| <
      |lengthInMeters height - other.displayedHeightInMeters|

/-!
The wall-incidence condition and horizontal kinematics determine the positive
impact time.  This is a derived result, not part of either law structure.
-/
lemma impactTime_eq_predicted
    (setup : BallWallProjectileSetup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_kinematics : SatisfiesIdealProjectileKinematics setup)
    (_impact : DescribesWallImpact setup) :
    timeInSeconds setup.impactTime =
      predictedImpactTimeInSeconds setup := by
  have hHorizontal :
      speedInMetersPerSecond setup.initialSpeed *
          Real.Angle.cos setup.launchAngle *
          timeInSeconds setup.impactTime =
        lengthInMeters setup.wallHorizontalDistance := by
    rw [← _kinematics.uniformHorizontalMotion setup.impactTime]
    exact _impact.impactIsAtWallHorizontalCoordinate
  have hVelocityNonzero :
      speedInMetersPerSecond setup.initialSpeed *
          Real.Angle.cos setup.launchAngle ≠ 0 :=
    mul_ne_zero _physical.initialSpeedPositive.ne'
      _physical.launchPointsRight.ne'
  rw [predictedImpactTimeInSeconds, eq_div_iff hVelocityNonzero]
  nlinarith

/-!
Substitution into the vertical kinematics gives the general impact-height
prediction without using any displayed answer.
-/
lemma impactHeight_eq_predicted
    (setup : BallWallProjectileSetup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_kinematics : SatisfiesIdealProjectileKinematics setup)
    (_impact : DescribesWallImpact setup) :
    lengthInMeters setup.impactHeightAboveRelease =
      predictedImpactHeightInMeters setup := by
  rw [predictedImpactHeightInMeters,
    ← impactTime_eq_predicted setup _physical _kinematics _impact,
    ← _impact.impactHeightIsVerticalDisplacement]
  exact _kinematics.verticalConstantGravityMotion setup.impactTime

/-!
With the source readouts and standard gravity, the independent impact height
equals the exact computed expression, lies within half a metre of `12.0 m`,
and choice C is uniquely closest among the four displayed values.

This formalizes blueprint label `thm:physics:phyx_mini_0740:target`.
-/
theorem problem_phyx_mini_0740
    (setup : BallWallProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_kinematics : SatisfiesIdealProjectileKinematics setup)
    (_impact : DescribesWallImpact setup) :
    lengthInMeters setup.impactHeightAboveRelease =
        computedImpactHeightInMeters ∧
      MatchesDisplayedHeight setup.impactHeightAboveRelease .C ∧
      IsUniqueClosestDisplayedHeight
        setup.impactHeightAboveRelease .C := by
  have hHeight :
      lengthInMeters setup.impactHeightAboveRelease =
        computedImpactHeightInMeters := by
    calc
      lengthInMeters setup.impactHeightAboveRelease =
          predictedImpactHeightInMeters setup :=
        impactHeight_eq_predicted setup _physical _kinematics _impact
      _ = computedImpactHeightInMeters := by
        simp only [predictedImpactHeightInMeters,
          predictedImpactTimeInSeconds,
          _description.initialSpeedMetersPerSecond,
          _description.launchAngleDegrees,
          _description.wallDistanceMeters,
          _gravity.gravityMetersPerSecondSquared,
          computedImpactHeightInMeters]
  let x : ℝ := 40 * Real.pi / 180
  let c : ℝ := Real.cos x
  let s : ℝ := Real.sin x
  have hxNonnegative : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxLessThanPiThird : x < Real.pi / 3 := by
    dsimp [x]
    nlinarith [Real.pi_pos]
  have hPiThirdLePi : Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcHalf : (1 / 2 : ℝ) < c := by
    dsimp [c]
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      hxNonnegative hPiThirdLePi hxLessThanPiThird
  have hTripleAngle : 3 * x = 2 * Real.pi / 3 := by
    dsimp [x]
    ring
  have hCosCubic : 4 * c ^ 3 - 3 * c = -(1 / 2 : ℝ) := by
    calc
      4 * c ^ 3 - 3 * c = Real.cos (3 * x) := by
        dsimp [c]
        exact (Real.cos_three_mul x).symm
      _ = Real.cos (2 * Real.pi / 3) := by rw [hTripleAngle]
      _ = -(1 / 2 : ℝ) := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
  have hcLower : (19 / 25 : ℝ) < c := by
    by_contra h
    have hDelta : c - (19 / 25 : ℝ) ≤ 0 := by
      linarith only [h]
    have hFactor :
        0 < 8 * (c ^ 2 + c * (19 / 25 : ℝ) +
          (19 / 25 : ℝ) ^ 2) - 6 := by
      nlinarith only [hcHalf, sq_nonneg c]
    have hProduct :
        (c - (19 / 25 : ℝ)) *
            (8 * (c ^ 2 + c * (19 / 25 : ℝ) +
              (19 / 25 : ℝ) ^ 2) - 6) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hDelta hFactor.le
    have hFactorization :
        (8 * c ^ 3 - 6 * c + 1) -
            (8 * (19 / 25 : ℝ) ^ 3 -
              6 * (19 / 25 : ℝ) + 1) =
          (c - (19 / 25 : ℝ)) *
            (8 * (c ^ 2 + c * (19 / 25 : ℝ) +
              (19 / 25 : ℝ) ^ 2) - 6) := by
      ring
    nlinarith only [hCosCubic, hProduct, hFactorization]
  have hcUpper : c < (96 / 125 : ℝ) := by
    by_contra h
    have hDelta : 0 ≤ c - (96 / 125 : ℝ) := by
      linarith only [h]
    have hFactor :
        0 < 8 * (c ^ 2 + c * (96 / 125 : ℝ) +
          (96 / 125 : ℝ) ^ 2) - 6 := by
      nlinarith only [hcHalf, sq_nonneg c]
    have hProduct :
        0 ≤ (c - (96 / 125 : ℝ)) *
            (8 * (c ^ 2 + c * (96 / 125 : ℝ) +
              (96 / 125 : ℝ) ^ 2) - 6) :=
      mul_nonneg hDelta hFactor.le
    have hFactorization :
        (8 * c ^ 3 - 6 * c + 1) -
            (8 * (96 / 125 : ℝ) ^ 3 -
              6 * (96 / 125 : ℝ) + 1) =
          (c - (96 / 125 : ℝ)) *
            (8 * (c ^ 2 + c * (96 / 125 : ℝ) +
              (96 / 125 : ℝ) ^ 2) - 6) := by
      ring
    nlinarith only [hCosCubic, hProduct, hFactorization]
  have hcPositive : 0 < c := by
    linarith only [hcHalf]
  have hxPositive : 0 < x := by
    dsimp [x]
    positivity
  have hxLessThanPi : x < Real.pi :=
    lt_of_lt_of_le hxLessThanPiThird hPiThirdLePi
  have hsPositive : 0 < s := by
    dsimp [s]
    exact Real.sin_pos_of_pos_of_lt_pi hxPositive hxLessThanPi
  have hSinCos : s ^ 2 + c ^ 2 = 1 := by
    dsimp [s, c]
    exact Real.sin_sq_add_cos_sq x
  have hcSquareUpper :
      c ^ 2 < (96 / 125 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hcPositive.le (by norm_num)).2 hcUpper
  have hcSquareLower :
      (19 / 25 : ℝ) ^ 2 < c ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hcPositive.le).2 hcLower
  have hsLower : (16 / 25 : ℝ) < s := by
    apply (sq_lt_sq₀ (by norm_num) hsPositive.le).1
    nlinarith only [hSinCos, hcSquareUpper]
  have hsUpper : s < (13 / 20 : ℝ) := by
    apply (sq_lt_sq₀ hsPositive.le (by norm_num)).1
    nlinarith only [hSinCos, hcSquareLower]
  have hSinCosProductLower :
      (16 / 25 : ℝ) * (19 / 25 : ℝ) < s * c := by
    calc
      (16 / 25 : ℝ) * (19 / 25 : ℝ) <
          (16 / 25 : ℝ) * c :=
        mul_lt_mul_of_pos_left hcLower (by norm_num)
      _ < s * c := mul_lt_mul_of_pos_right hsLower hcPositive
  have hSinCosProductUpper :
      s * c < (13 / 20 : ℝ) * (96 / 125 : ℝ) := by
    calc
      s * c < (13 / 20 : ℝ) * c :=
        mul_lt_mul_of_pos_right hsUpper hcPositive
      _ < (13 / 20 : ℝ) * (96 / 125 : ℝ) :=
        mul_lt_mul_of_pos_left hcUpper (by norm_num)
  have hComputedFormula :
      computedImpactHeightInMeters =
        (22 * s * c - (11858 / 3125 : ℝ)) / c ^ 2 := by
    simp only [computedImpactHeightInMeters, degrees,
      Real.Angle.sin_coe, Real.Angle.cos_coe]
    change
      25 * s * (22 / (25 * c)) -
          (1 / 2 : ℝ) * (49 / 5 : ℝ) *
            (22 / (25 * c)) ^ 2 =
        (22 * s * c - (11858 / 3125 : ℝ)) / c ^ 2
    field_simp [hcPositive.ne']
    ring
  have hcSquarePositive : 0 < c ^ 2 := sq_pos_of_pos hcPositive
  have hLowerNumerator :
      (23 / 2 : ℝ) * c ^ 2 <
        22 * s * c - (11858 / 3125 : ℝ) := by
    nlinarith only [hSinCosProductLower, hcSquareUpper]
  have hUpperNumerator :
      22 * s * c - (11858 / 3125 : ℝ) <
        (25 / 2 : ℝ) * c ^ 2 := by
    nlinarith only [hSinCosProductUpper, hcSquareLower]
  have hComputedInterval :
      (23 / 2 : ℝ) < computedImpactHeightInMeters ∧
        computedImpactHeightInMeters < (25 / 2 : ℝ) := by
    rw [hComputedFormula]
    exact ⟨(lt_div_iff₀ hcSquarePositive).2 hLowerNumerator,
      (div_lt_iff₀ hcSquarePositive).2 hUpperNumerator⟩
  have hComputedClose :
      |computedImpactHeightInMeters - 12| < (1 / 2 : ℝ) := by
    rw [abs_lt]
    constructor <;>
      linarith only [hComputedInterval.1, hComputedInterval.2]
  refine ⟨hHeight, ?_, ?_⟩
  · simpa [MatchesDisplayedHeight,
      AnswerChoice.displayedHeightInMeters, hHeight] using hComputedClose
  · intro other hOther
    rw [hHeight]
    cases other with
    | A =>
        simp only [AnswerChoice.displayedHeightInMeters]
        calc
          |computedImpactHeightInMeters - 12| < (1 / 2 : ℝ) :=
            hComputedClose
          _ < computedImpactHeightInMeters - 8 := by
            linarith only [hComputedInterval.1]
          _ = |computedImpactHeightInMeters - 8| := by
            rw [abs_of_pos]
            linarith only [hComputedInterval.1]
    | B =>
        simp only [AnswerChoice.displayedHeightInMeters]
        calc
          |computedImpactHeightInMeters - 12| < (1 / 2 : ℝ) :=
            hComputedClose
          _ < computedImpactHeightInMeters - 10 := by
            linarith only [hComputedInterval.1]
          _ = |computedImpactHeightInMeters - 10| := by
            rw [abs_of_pos]
            linarith only [hComputedInterval.1]
    | C =>
        exact (hOther rfl).elim
    | D =>
        simp only [AnswerChoice.displayedHeightInMeters]
        calc
          |computedImpactHeightInMeters - 12| < (1 / 2 : ℝ) :=
            hComputedClose
          _ < -(computedImpactHeightInMeters - 14) := by
            linarith only [hComputedInterval.2]
          _ = |computedImpactHeightInMeters - 14| := by
            exact (abs_of_neg (by
              linarith only [hComputedInterval.2])).symm

end PhyXMiniProblems.ProblemPhyXMini0740
