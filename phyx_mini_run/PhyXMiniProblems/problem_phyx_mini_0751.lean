import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0751

open Dimension

/-!
# Initial speed for a basketball foul shot

The primary raster shows a basketball released at height `h₁`, a hoop center
at height `h₂`, a short horizontal offset `d₁` from the player's datum to the
release point, and a total horizontal distance `d₂` from the same datum to the
hoop. Thus the ball travels horizontally through `d₂ - d₁`. The problem gives
`d₁ = 1 ft`, `d₂ = 14 ft`, `h₁ = 7 ft`, `h₂ = 10 ft`, and launch angle
`θ₀ = 55°` above the horizontal.

Lengths, durations, speeds, and acceleration magnitudes below are genuine
unit-independent Physlib quantities. Real numbers occur only as unit readouts,
dimensionless trigonometric values, and displayed numerical answers. The
launch speed is an independent field constrained by projectile kinematics and
the hoop boundary condition; it is not defined from the recorded answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, independent of its readout unit. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Foot readout of a physical length. -/
def lengthInFeet (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.feet length

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Foot-per-second readout of a physical speed. -/
def speedInFeetPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.feet TimeUnit.seconds speed

/-- Foot-per-second-squared readout of an acceleration magnitude. -/
def accelerationInFeetPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.feet TimeUnit.seconds acceleration

/-- Convert a numerical degree readout into Mathlib's angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Scenario and primary-figure vocabulary -/

/-- The elementary flight idealization used after the ball is released. -/
inductive FlightModel where
  | uniformDownwardGravityNegligibleDrag
  | other
  deriving DecidableEq, Repr

/-- The reference direction from which the launch angle is measured. -/
inductive LaunchAngleReference where
  | horizontalCourtSurface
  | other
  deriving DecidableEq, Repr

/-- Objects and drawn features visibly distinguished in the source raster. -/
inductive FigureObject where
  | player
  | releasedBasketball
  | basketballAtHoop
  | trajectoryArc
  | hoopRim
  | net
  | backboard
  | courtFloor
  deriving DecidableEq, Fintype, Repr

/-- The four physical-length labels printed in the raster. -/
inductive FigureLengthLabel where
  | dOne
  | dTwo
  | hOne
  | hTwo
  deriving DecidableEq, Fintype, Repr

/-- The launch-angle label printed beside the released ball. -/
inductive FigureAngleLabel where
  | thetaZero
  deriving DecidableEq, Fintype, Repr

/-- Geometric point roles needed to identify endpoints of the figure labels. -/
inductive FigurePoint where
  | playerHorizontalDatum
  | floorBelowRelease
  | ballReleasePoint
  | floorBelowHoop
  | hoopCenter
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and label-denotation information from image `751.png`.
The raster prints the symbols `d₁`, `d₂`, `h₁`, `h₂`, and `θ₀`; their
numerical values are supplied by the prose and recorded separately below.
-/
structure BasketballFoulShotFigure where
  showsObject : FigureObject → Bool
  showsLengthLabel : FigureLengthLabel → Bool
  showsAngleLabel : FigureAngleLabel → Bool
  measuredLength : FigureLengthLabel → LengthQuantity
  measuredAngle : FigureAngleLabel → Real.Angle
  lengthLineEndpoints : FigureLengthLabel → FigurePoint × FigurePoint
  angleVertex : FigureAngleLabel → FigurePoint
  floorIsHorizontal : Bool
  trajectoryIsParabolicArc : Bool
  trajectoryStartsAtReleasedBall : Bool
  trajectoryEndsAtHoop : Bool
  hoopIsToRightOfRelease : Bool

/-!
Independent physical quantities and trajectory observables for the shot.
Horizontal displacement is measured from the vertical line through the
release point, while vertical position is height above the court floor.
Neither crossing time nor launch speed is defined from an answer.
-/
structure BasketballFoulShotSetup where
  figure : BasketballFoulShotFigure
  playerDatumToReleaseOffset : LengthQuantity
  playerDatumToHoopDistance : LengthQuantity
  releaseToHoopHorizontalDistance : LengthQuantity
  releaseHeight : LengthQuantity
  hoopCenterHeight : LengthQuantity
  launchSpeed : SpeedQuantity
  launchAngle : Real.Angle
  gravitationalAcceleration : AccelerationQuantity
  hoopCrossingTime : TimeQuantity
  horizontalDisplacementFromReleaseAt : TimeQuantity → LengthQuantity
  heightAboveFloorAt : TimeQuantity → LengthQuantity
  flightModel : FlightModel
  launchAngleReference : LaunchAngleReference

/-!
The qualitative idealization implicit in the textbook problem. This contains
no numerical speed or answer-choice information.
-/
structure MatchesFoulShotScenario
    (setup : BasketballFoulShotSetup) : Prop where
  idealFlightModel :
    setup.flightModel = .uniformDownwardGravityNegligibleDrag
  angleMeasuredAboveHorizontal :
    setup.launchAngleReference = .horizontalCourtSurface

/-!
Exact numerical readouts from the prose. The first two distances share the
player datum shown in the figure. The unknown speed and crossing time are
deliberately absent.
-/
structure MatchesProblemReadouts
    (setup : BasketballFoulShotSetup) : Prop where
  dOneFeet : lengthInFeet setup.playerDatumToReleaseOffset = 1
  dTwoFeet : lengthInFeet setup.playerDatumToHoopDistance = 14
  hOneFeet : lengthInFeet setup.releaseHeight = 7
  hTwoFeet : lengthInFeet setup.hoopCenterHeight = 10
  thetaZeroDegrees : setup.launchAngle = degrees 55

/-!
Exact qualitative and incidence evidence from the primary raster. In
particular, `d₁` ends below the release point and `d₂` ends below the hoop, so
their difference is the ball's horizontal displacement to the hoop. This
contains no launch-speed value.
-/
structure MatchesSuppliedFigure
    (setup : BasketballFoulShotSetup) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLengthLabelShown :
    ∀ label : FigureLengthLabel, setup.figure.showsLengthLabel label = true
  everyAngleLabelShown :
    ∀ label : FigureAngleLabel, setup.figure.showsAngleLabel label = true
  dOneDenotesPlayerToReleaseOffset :
    setup.figure.measuredLength .dOne = setup.playerDatumToReleaseOffset
  dTwoDenotesPlayerToHoopDistance :
    setup.figure.measuredLength .dTwo = setup.playerDatumToHoopDistance
  hOneDenotesReleaseHeight :
    setup.figure.measuredLength .hOne = setup.releaseHeight
  hTwoDenotesHoopHeight :
    setup.figure.measuredLength .hTwo = setup.hoopCenterHeight
  thetaZeroDenotesLaunchAngle :
    setup.figure.measuredAngle .thetaZero = setup.launchAngle
  dOneEndpoints :
    setup.figure.lengthLineEndpoints .dOne =
      (.playerHorizontalDatum, .floorBelowRelease)
  dTwoEndpoints :
    setup.figure.lengthLineEndpoints .dTwo =
      (.playerHorizontalDatum, .floorBelowHoop)
  hOneEndpoints :
    setup.figure.lengthLineEndpoints .hOne =
      (.floorBelowRelease, .ballReleasePoint)
  hTwoEndpoints :
    setup.figure.lengthLineEndpoints .hTwo =
      (.floorBelowHoop, .hoopCenter)
  thetaZeroVertex :
    setup.figure.angleVertex .thetaZero = .ballReleasePoint
  horizontalDistanceDecomposition :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.playerDatumToHoopDistance =
        lengthReadout unit setup.playerDatumToReleaseOffset +
          lengthReadout unit setup.releaseToHoopHorizontalDistance
  floorHorizontal : setup.figure.floorIsHorizontal = true
  pathIsParabolic : setup.figure.trajectoryIsParabolicArc = true
  pathStartsAtReleasedBall :
    setup.figure.trajectoryStartsAtReleasedBall = true
  pathEndsAtHoop : setup.figure.trajectoryEndsAtHoop = true
  hoopRightOfRelease : setup.figure.hoopIsToRightOfRelease = true

/-!
The standard near-Earth gravity calibration used with customary US units in
this elementary exercise. It is environmental data, not a speed conclusion.
-/
structure UsesStandardNearEarthGravity
    (setup : BasketballFoulShotSetup) : Prop where
  gravityFeetPerSecondSquared :
    accelerationInFeetPerSecondSquared setup.gravitationalAcceleration = 32

/-!
Positivity and the acute, forward, upward launch branch drawn in the raster.
These conditions contain no numerical launch-speed result.
-/
structure HasPhysicalFoulShotParameters
    (setup : BasketballFoulShotSetup) : Prop where
  playerToReleaseOffsetPositive :
    0 < lengthInFeet setup.playerDatumToReleaseOffset
  playerToHoopDistancePositive :
    0 < lengthInFeet setup.playerDatumToHoopDistance
  releaseToHoopDistancePositive :
    0 < lengthInFeet setup.releaseToHoopHorizontalDistance
  releaseHeightPositive : 0 < lengthInFeet setup.releaseHeight
  hoopHeightPositive : 0 < lengthInFeet setup.hoopCenterHeight
  launchSpeedPositive : 0 < speedInFeetPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInFeetPerSecondSquared setup.gravitationalAcceleration
  hoopCrossingTimePositive : 0 < timeInSeconds setup.hoopCrossingTime
  forwardHorizontalComponent : 0 < Real.Angle.cos setup.launchAngle
  upwardInitialComponent : 0 < Real.Angle.sin setup.launchAngle

/-!
The two component equations for ideal projectile motion, stated in every
coherent choice of length and time units. They are general governing laws and
do not mention the hoop boundary, an answer choice, or `23 ft/s`.
-/
structure SatisfiesIdealProjectileMotion
    (setup : BasketballFoulShotSetup) : Prop where
  horizontalTrajectory :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (elapsed : TimeQuantity),
      timeInSeconds elapsed ≤ timeInSeconds setup.hoopCrossingTime →
        lengthReadout lengthUnit
            (setup.horizontalDisplacementFromReleaseAt elapsed) =
          speedReadout lengthUnit timeUnit setup.launchSpeed *
            Real.Angle.cos setup.launchAngle *
            timeReadout timeUnit elapsed
  verticalTrajectory :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (elapsed : TimeQuantity),
      timeInSeconds elapsed ≤ timeInSeconds setup.hoopCrossingTime →
        lengthReadout lengthUnit (setup.heightAboveFloorAt elapsed) =
          lengthReadout lengthUnit setup.releaseHeight +
            speedReadout lengthUnit timeUnit setup.launchSpeed *
              Real.Angle.sin setup.launchAngle *
              timeReadout timeUnit elapsed -
            (1 / 2 : ℝ) *
              accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration *
              timeReadout timeUnit elapsed ^ 2

/-!
The boundary condition expressed by "make the foul shot": at a positive
crossing time, the idealized center of the ball is at the hoop center. This is
event geometry, not the requested launch-speed conclusion.
-/
structure PassesThroughHoop (setup : BasketballFoulShotSetup) : Prop where
  horizontalCoordinateAtHoop :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.horizontalDisplacementFromReleaseAt setup.hoopCrossingTime) =
        lengthReadout unit setup.releaseToHoopHorizontalDistance
  verticalCoordinateAtHoop :
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.heightAboveFloorAt setup.hoopCrossingTime) =
        lengthReadout unit setup.hoopCenterHeight

/-! ## Derived ballistic relations and answer metadata -/

/-!
The generic launch-speed expression obtained by eliminating crossing time
from the component equations. It does not define `setup.launchSpeed`; equality
to that independent physical quantity is a substantive conclusion.
-/
def idealRequiredSpeedInFeetPerSecond
    (setup : BasketballFoulShotSetup) : ℝ :=
  Real.sqrt
    (accelerationInFeetPerSecondSquared setup.gravitationalAcceleration *
        lengthInFeet setup.releaseToHoopHorizontalDistance ^ 2 /
      (2 * Real.Angle.cos setup.launchAngle ^ 2 *
        (lengthInFeet setup.releaseToHoopHorizontalDistance *
            Real.Angle.sin setup.launchAngle /
            Real.Angle.cos setup.launchAngle -
          (lengthInFeet setup.hoopCenterHeight -
            lengthInFeet setup.releaseHeight))))

/-- The two horizontal figure readouts imply a `13 ft` flight displacement. -/
lemma releaseToHoopHorizontalDistanceInFeet_eq
    (setup : BasketballFoulShotSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup) :
    lengthInFeet setup.releaseToHoopHorizontalDistance = 13 := by
  have hDecomposition :=
    hFigure.horizontalDistanceDecomposition LengthUnit.feet
  have hdOne :
      lengthReadout LengthUnit.feet setup.playerDatumToReleaseOffset = 1 := by
    simpa [lengthInFeet] using hReadouts.dOneFeet
  have hdTwo :
      lengthReadout LengthUnit.feet setup.playerDatumToHoopDistance = 14 := by
    simpa [lengthInFeet] using hReadouts.dTwoFeet
  rw [hdTwo, hdOne] at hDecomposition
  simpa [lengthInFeet] using (show
    lengthReadout LengthUnit.feet setup.releaseToHoopHorizontalDistance = 13 by
      linarith)

/-- The horizontal component equation fixes the positive hoop-crossing time. -/
lemma hoopCrossingTimeInSeconds_eq
    (setup : BasketballFoulShotSetup)
    (hPhysical : HasPhysicalFoulShotParameters setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hHoop : PassesThroughHoop setup) :
    timeInSeconds setup.hoopCrossingTime =
      lengthInFeet setup.releaseToHoopHorizontalDistance /
        (speedInFeetPerSecond setup.launchSpeed *
          Real.Angle.cos setup.launchAngle) := by
  have hTrajectory :=
    hMotion.horizontalTrajectory LengthUnit.feet TimeUnit.seconds
      setup.hoopCrossingTime le_rfl
  have hEq :
      lengthInFeet setup.releaseToHoopHorizontalDistance =
        speedInFeetPerSecond setup.launchSpeed *
          Real.Angle.cos setup.launchAngle *
            timeInSeconds setup.hoopCrossingTime := by
    change
      lengthReadout LengthUnit.feet setup.releaseToHoopHorizontalDistance =
        speedReadout LengthUnit.feet TimeUnit.seconds setup.launchSpeed *
          Real.Angle.cos setup.launchAngle *
            timeReadout TimeUnit.seconds setup.hoopCrossingTime
    rw [← hHoop.horizontalCoordinateAtHoop LengthUnit.feet]
    exact hTrajectory
  have hComponentPos :
      0 < speedInFeetPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle :=
    mul_pos hPhysical.launchSpeedPositive hPhysical.forwardHorizontalComponent
  apply (eq_div_iff hComponentPos.ne').2
  nlinarith

/-!
Eliminating the crossing time gives the exact required speed relation before
substituting the problem's numerical readouts.
-/
lemma launchSpeed_eq_idealRequiredSpeed
    (setup : BasketballFoulShotSetup)
    (hPhysical : HasPhysicalFoulShotParameters setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hHoop : PassesThroughHoop setup) :
    speedInFeetPerSecond setup.launchSpeed =
      idealRequiredSpeedInFeetPerSecond setup := by
  let v := speedInFeetPerSecond setup.launchSpeed
  let c := Real.Angle.cos setup.launchAngle
  let s := Real.Angle.sin setup.launchAngle
  let t := timeInSeconds setup.hoopCrossingTime
  let x := lengthInFeet setup.releaseToHoopHorizontalDistance
  let y₀ := lengthInFeet setup.releaseHeight
  let yₕ := lengthInFeet setup.hoopCenterHeight
  let g := accelerationInFeetPerSecondSquared
    setup.gravitationalAcceleration
  let denominator := 2 * c ^ 2 * (x * s / c - (yₕ - y₀))
  have hv : 0 < v := hPhysical.launchSpeedPositive
  have hc : 0 < c := hPhysical.forwardHorizontalComponent
  have ht : 0 < t := hPhysical.hoopCrossingTimePositive
  have hg : 0 < g := hPhysical.gravityPositive
  have hHorizontal : x = v * c * t := by
    have hTrajectory :=
      hMotion.horizontalTrajectory LengthUnit.feet TimeUnit.seconds
        setup.hoopCrossingTime le_rfl
    dsimp [x, v, c, t]
    change
      lengthReadout LengthUnit.feet setup.releaseToHoopHorizontalDistance =
        speedReadout LengthUnit.feet TimeUnit.seconds setup.launchSpeed *
          Real.Angle.cos setup.launchAngle *
            timeReadout TimeUnit.seconds setup.hoopCrossingTime
    rw [← hHoop.horizontalCoordinateAtHoop LengthUnit.feet]
    exact hTrajectory
  have hVertical : yₕ = y₀ + v * s * t - (1 / 2 : ℝ) * g * t ^ 2 := by
    have hTrajectory :=
      hMotion.verticalTrajectory LengthUnit.feet TimeUnit.seconds
        setup.hoopCrossingTime le_rfl
    dsimp [yₕ, y₀, v, s, t, g]
    change
      lengthReadout LengthUnit.feet setup.hoopCenterHeight =
        lengthReadout LengthUnit.feet setup.releaseHeight +
          speedReadout LengthUnit.feet TimeUnit.seconds setup.launchSpeed *
            Real.Angle.sin setup.launchAngle *
              timeReadout TimeUnit.seconds setup.hoopCrossingTime -
          (1 / 2 : ℝ) *
            accelerationReadout LengthUnit.feet TimeUnit.seconds
              setup.gravitationalAcceleration *
            timeReadout TimeUnit.seconds setup.hoopCrossingTime ^ 2
    rw [← hHoop.verticalCoordinateAtHoop LengthUnit.feet]
    exact hTrajectory
  have hTangentTerm : x * s / c = v * s * t := by
    rw [hHorizontal]
    field_simp [hc.ne']
  have hHeightDifference :
      yₕ - y₀ = v * s * t - (1 / 2 : ℝ) * g * t ^ 2 := by
    linarith
  have hBracket :
      x * s / c - (yₕ - y₀) = (1 / 2 : ℝ) * g * t ^ 2 := by
    linarith
  have hDenominator : denominator = g * c ^ 2 * t ^ 2 := by
    dsimp [denominator]
    rw [hBracket]
    ring
  have hDenominatorPos : 0 < denominator := by
    rw [hDenominator]
    positivity
  have hBallistic : v ^ 2 * denominator = g * x ^ 2 := by
    rw [hDenominator, hHorizontal]
    ring
  have hRadicand : g * x ^ 2 / denominator = v ^ 2 := by
    apply (div_eq_iff hDenominatorPos.ne').2
    nlinarith
  change v = Real.sqrt (g * x ^ 2 / denominator)
  rw [hRadicand, Real.sqrt_sq_eq_abs, abs_of_pos hv]

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in feet per second printed beside each answer label. -/
def displayedAnswerSpeedInFeetPerSecond : AnswerChoice → ℝ
  | .A => 18
  | .B => 20
  | .C => 23
  | .D => 26

/-- Dataset answer metadata; this definition is not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a whole-foot-per-second display by ordinary rounding. -/
def RoundsToNearestFootPerSecond
    (speed : SpeedQuantity) (displayedValue : ℝ) : Prop :=
  |speedInFeetPerSecond speed - displayedValue| < (1 / 2 : ℝ)

/-- The physical launch speed agrees with the value printed for a choice. -/
def MatchesAnswerChoice
    (setup : BasketballFoulShotSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestFootPerSecond setup.launchSpeed
    (displayedAnswerSpeedInFeetPerSecond choice)

/-- Absolute error between the required speed and a displayed choice. -/
def displayedChoiceError
    (setup : BasketballFoulShotSetup) (choice : AnswerChoice) : ℝ :=
  |speedInFeetPerSecond setup.launchSpeed -
    displayedAnswerSpeedInFeetPerSecond choice|

/-- A choice is at least as close as every listed alternative. -/
def IsClosestDisplayedSpeedChoice
    (setup : BasketballFoulShotSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    displayedChoiceError setup choice ≤ displayedChoiceError setup other

/-- A choice is the unique closest listed speed. -/
def IsUniqueClosestDisplayedSpeedChoice
    (setup : BasketballFoulShotSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedSpeedChoice setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedSpeedChoice setup other → other = choice

/-!
The figure geometry gives a horizontal flight distance of `14 - 1 = 13 ft`.
The projectile equations then give

`v = sqrt (g x² / (2 cos² θ (x tan θ - (h₂ - h₁))))`.

With `x = 13 ft`, `h₂ - h₁ = 3 ft`, `θ = 55°`, and
`g = 32 ft/s²`, this speed is approximately `23 ft/s`. It rounds to the
unique closest displayed value, answer C.

The displacement, exact speed relation, rounding statement, and answer
selection are all conclusions rather than fields of a scenario, readout,
figure, gravity, positivity, motion-law, or hoop-boundary premise.

Blueprint label: `thm:physics:phyx_mini_0751:target`.
-/
theorem problem_phyx_mini_0751
    (setup : BasketballFoulShotSetup)
    (hScenario : MatchesFoulShotScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hPhysical : HasPhysicalFoulShotParameters setup)
    (hMotion : SatisfiesIdealProjectileMotion setup)
    (hHoop : PassesThroughHoop setup) :
    lengthInFeet setup.releaseToHoopHorizontalDistance = 13 ∧
      speedInFeetPerSecond setup.launchSpeed =
        idealRequiredSpeedInFeetPerSecond setup ∧
      RoundsToNearestFootPerSecond setup.launchSpeed 23 ∧
      MatchesAnswerChoice setup .C ∧
      IsUniqueClosestDisplayedSpeedChoice setup .C := by
  set_option maxHeartbeats 500000 in
    have hDistance :=
      releaseToHoopHorizontalDistanceInFeet_eq setup hReadouts hFigure
    have hExactSpeed :=
      launchSpeed_eq_idealRequiredSpeed setup hPhysical hMotion hHoop
  
    let q : ℝ := Real.cos (Real.pi / 9)
    let r : ℝ := Real.sin (Real.pi / 9)
    have hqHalf : (1 / 2 : ℝ) < q := by
      dsimp [q]
      rw [← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi
        (by positivity)
        (by nlinarith only [Real.pi_pos])
        (by nlinarith only [Real.pi_pos])
    have hqNonneg : 0 ≤ q := by
      exact (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans hqHalf.le
    have hqCubic : 4 * q ^ 3 - 3 * q = (1 / 2 : ℝ) := by
      dsimp [q]
      calc
        4 * Real.cos (Real.pi / 9) ^ 3 -
              3 * Real.cos (Real.pi / 9) =
            Real.cos (3 * (Real.pi / 9)) :=
          (Real.cos_three_mul _).symm
        _ = Real.cos (Real.pi / 3) := by congr 1 <;> ring
        _ = 1 / 2 := Real.cos_pi_div_three
    have hqLower : (939 / 1000 : ℝ) < q := by
      by_contra h
      have hLe : q ≤ (939 / 1000 : ℝ) := le_of_not_gt h
      have hp :
          0 ≤ (q - (1 / 2 : ℝ)) * (q + 939 / 500) ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hqHalf.le) (sq_nonneg _)
      nlinarith only [hqCubic, hLe, hp]
    have hqUpper : q < (47 / 50 : ℝ) := by
      by_contra h
      have hGe : (47 / 50 : ℝ) ≤ q := le_of_not_gt h
      have hp :
          0 ≤ (q - (47 / 50 : ℝ)) * (q + 47 / 25) ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hGe) (sq_nonneg _)
      nlinarith only [hqCubic, hGe, hp]
    have hrNonneg : 0 ≤ r := by
      dsimp [r]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
    have hqr : q ^ 2 + r ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq (Real.pi / 9)
    have hrLower : (17 / 50 : ℝ) < r := by
      by_contra h
      have hrLe : r ≤ (17 / 50 : ℝ) := le_of_not_gt h
      have hrSqLe : r ^ 2 ≤ (17 / 50 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hrNonneg hrLe 2
      have hqSqLt : q ^ 2 < (47 / 50 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hqUpper hqNonneg (by norm_num)
      nlinarith only [hqr, hrSqLe, hqSqLt]
    have hrUpper : r < (7 / 20 : ℝ) := by
      by_contra h
      have hrGe : (7 / 20 : ℝ) ≤ r := le_of_not_gt h
      have hrSqGe : (7 / 20 : ℝ) ^ 2 ≤ r ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hrGe 2
      have hqSqGt : (939 / 1000 : ℝ) ^ 2 < q ^ 2 :=
        pow_lt_pow_left₀ hqLower (by norm_num) (by norm_num)
      nlinarith only [hqr, hrSqGe, hqSqGt]

    let c : ℝ := Real.Angle.cos (degrees 55)
    let s : ℝ := Real.Angle.sin (degrees 55)
    have hTwoCS : 2 * c * s = q := by
      dsimp [c, s, degrees, q]
      calc
        2 * Real.cos (55 * Real.pi / 180) *
              Real.sin (55 * Real.pi / 180) =
            2 * Real.sin (55 * Real.pi / 180) *
              Real.cos (55 * Real.pi / 180) := by ring
        _ = Real.sin (2 * (55 * Real.pi / 180)) :=
          (Real.sin_two_mul _).symm
        _ = Real.sin (Real.pi / 9 + Real.pi / 2) := by
          congr 1 <;> ring
        _ = Real.cos (Real.pi / 9) := Real.sin_add_pi_div_two _
    have hTwoCSq : 2 * c ^ 2 = 1 - r := by
      dsimp [c, degrees, r]
      calc
        2 * Real.cos (55 * Real.pi / 180) ^ 2 =
            Real.cos (2 * (55 * Real.pi / 180)) + 1 := by
          rw [Real.cos_two_mul]
          ring
        _ = Real.cos (Real.pi / 9 + Real.pi / 2) + 1 := by
          congr 2 <;> ring
        _ = -Real.sin (Real.pi / 9) + 1 := by
          rw [Real.cos_add_pi_div_two]
        _ = 1 - Real.sin (Real.pi / 9) := by ring

    let ballisticDenominator : ℝ := 26 * c * s - 6 * c ^ 2
    have hcPos : 0 < c := by
      dsimp only [c]
      rw [← hReadouts.thetaZeroDegrees]
      exact hPhysical.forwardHorizontalComponent
    have hDenominatorIdentity :
        ballisticDenominator = 13 * q + 3 * r - 3 := by
      dsimp only [ballisticDenominator]
      nlinarith only [hTwoCS, hTwoCSq]
    have hDenominatorBounds :
        (99 / 10 : ℝ) < ballisticDenominator ∧
          ballisticDenominator < (211 / 20 : ℝ) := by
      rw [hDenominatorIdentity]
      constructor <;>
        nlinarith only [hqLower, hqUpper, hrLower, hrUpper]
    have hDenominatorPos : 0 < ballisticDenominator :=
      (by norm_num : (0 : ℝ) < 99 / 10).trans
        hDenominatorBounds.1
    have hSpeedFormula :
        speedInFeetPerSecond setup.launchSpeed =
          Real.sqrt (5408 / ballisticDenominator) := by
      rw [hExactSpeed]
      unfold idealRequiredSpeedInFeetPerSecond
      rw [hGravity.gravityFeetPerSecondSquared, hDistance,
        hReadouts.hTwoFeet, hReadouts.hOneFeet, hReadouts.thetaZeroDegrees]
      congr 1
      change
        32 * 13 ^ 2 /
            (2 * c ^ 2 * (13 * s / c - (10 - 7))) =
          5408 / ballisticDenominator
      have hcNe : c ≠ 0 := hcPos.ne'
      have hDenominatorIdentity :
          2 * c ^ 2 * (13 * s / c - (10 - 7)) =
            ballisticDenominator := by
        dsimp only [ballisticDenominator]
        rw [show (10 : ℝ) - 7 = 3 by norm_num]
        rw [show
          2 * c ^ 2 * (13 * s / c - 3) =
              2 * c * ((13 * s / c) * c) - 6 * c ^ 2 by ring]
        have hCancel : (13 * s / c) * c = 13 * s :=
          div_mul_cancel₀ (13 * s) hcNe
        calc
          2 * c * ((13 * s / c) * c) - 6 * c ^ 2 =
              2 * c * (13 * s) - 6 * c ^ 2 :=
            congrArg (fun q : ℝ => 2 * c * q - 6 * c ^ 2) hCancel
          _ = 26 * c * s - 6 * c ^ 2 := by ring
      rw [show (32 : ℝ) * 13 ^ 2 = 5408 by norm_num,
        hDenominatorIdentity]
    let v : ℝ := speedInFeetPerSecond setup.launchSpeed
    have hvPos : 0 < v := hPhysical.launchSpeedPositive
    have hvSq : v ^ 2 = 5408 / ballisticDenominator := by
      dsimp only [v]
      rw [hSpeedFormula]
      exact Real.sq_sqrt (div_nonneg (by norm_num) hDenominatorPos.le)
    have hvBallistic : v ^ 2 * ballisticDenominator = 5408 := by
      rw [hvSq]
      exact div_mul_cancel₀ 5408 hDenominatorPos.ne'
    have hvLower : (45 / 2 : ℝ) < v := by
      by_contra h
      have hvLe : v ≤ (45 / 2 : ℝ) := le_of_not_gt h
      have hvSqLe : v ^ 2 ≤ (45 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hvPos.le hvLe 2
      have hProductLe := mul_le_mul_of_nonneg_right hvSqLe hDenominatorPos.le
      have hProductLt := mul_lt_mul_of_pos_left hDenominatorBounds.2
        (show 0 < (45 / 2 : ℝ) ^ 2 by positivity)
      have hLt5408 :
          v ^ 2 * ballisticDenominator < (5408 : ℝ) :=
        hProductLe.trans_lt
          (hProductLt.trans
            (show
              (45 / 2 : ℝ) ^ 2 * (211 / 20) < 5408 by norm_num))
      rw [hvBallistic] at hLt5408
      exact (lt_irrefl 5408 hLt5408)
    have hvUpper : v < (47 / 2 : ℝ) := by
      by_contra h
      have hvGe : (47 / 2 : ℝ) ≤ v := le_of_not_gt h
      have hvSqGe : (47 / 2 : ℝ) ^ 2 ≤ v ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hvGe 2
      have hProductGe := mul_le_mul_of_nonneg_right hvSqGe hDenominatorPos.le
      have hProductGt := mul_lt_mul_of_pos_left hDenominatorBounds.1
        (show 0 < (47 / 2 : ℝ) ^ 2 by positivity)
      have h5408Lt :
          (5408 : ℝ) < v ^ 2 * ballisticDenominator :=
        ((show
            (5408 : ℝ) < (47 / 2) ^ 2 * (99 / 10) by norm_num).trans
          hProductGt).trans_le hProductGe
      rw [hvBallistic] at h5408Lt
      exact (lt_irrefl 5408 h5408Lt)
    set_option maxHeartbeats 400000 in
      have hRounds : RoundsToNearestFootPerSecond setup.launchSpeed 23 := by
        rw [RoundsToNearestFootPerSecond, abs_lt]
        change -(1 / 2 : ℝ) < v - 23 ∧ v - 23 < (1 / 2 : ℝ)
        constructor
        · convert sub_lt_sub_right hvLower 23 using 1 <;> norm_num
        · convert sub_lt_sub_right hvUpper 23 using 1 <;> norm_num
      have hMatchesC : MatchesAnswerChoice setup .C := by
        change RoundsToNearestFootPerSecond setup.launchSpeed 23
        exact hRounds
      have hErrorBound : |v - 23| < (1 / 2 : ℝ) := by
        change |v - 23| < (1 / 2 : ℝ) at hRounds
        exact hRounds
      have hClosestC : IsClosestDisplayedSpeedChoice setup .C := by
        intro other
        cases other with
        | A =>
            unfold displayedChoiceError
            simp only [displayedAnswerSpeedInFeetPerSecond]
            change |v - 23| ≤ |v - 18|
            have hGap : (1 / 2 : ℝ) < v - 18 :=
              (by norm_num : (1 / 2 : ℝ) < 45 / 2 - 18).trans
                (sub_lt_sub_right hvLower 18)
            rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1 / 2).trans hGap)]
            exact hErrorBound.le.trans hGap.le
        | B =>
            unfold displayedChoiceError
            simp only [displayedAnswerSpeedInFeetPerSecond]
            change |v - 23| ≤ |v - 20|
            have hGap : (1 / 2 : ℝ) < v - 20 :=
              (by norm_num : (1 / 2 : ℝ) < 45 / 2 - 20).trans
                (sub_lt_sub_right hvLower 20)
            rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1 / 2).trans hGap)]
            exact hErrorBound.le.trans hGap.le
        | C => exact le_rfl
        | D =>
            unfold displayedChoiceError
            simp only [displayedAnswerSpeedInFeetPerSecond]
            change |v - 23| ≤ |v - 26|
            have hGap : (1 / 2 : ℝ) < 26 - v :=
              (by norm_num : (1 / 2 : ℝ) < 26 - 47 / 2).trans
                (sub_lt_sub_left hvUpper 26)
            have hv26 : v < 26 :=
              hvUpper.trans (by norm_num)
            rw [abs_of_neg (sub_neg.mpr hv26)]
            simpa only [neg_sub] using hErrorBound.le.trans hGap.le
      have hUniqueC : IsUniqueClosestDisplayedSpeedChoice setup .C := by
        refine ⟨hClosestC, ?_⟩
        intro other hOther
        cases other with
        | A =>
            have hAgainst := hOther .C
            unfold displayedChoiceError at hAgainst
            simp only [displayedAnswerSpeedInFeetPerSecond] at hAgainst
            change |v - 18| ≤ |v - 23| at hAgainst
            have hGap : (1 / 2 : ℝ) < v - 18 :=
              (by norm_num : (1 / 2 : ℝ) < 45 / 2 - 18).trans
                (sub_lt_sub_right hvLower 18)
            rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1 / 2).trans hGap)]
              at hAgainst
            exact False.elim
              (lt_irrefl _ ((hGap.trans_le hAgainst).trans hErrorBound))
        | B =>
            have hAgainst := hOther .C
            unfold displayedChoiceError at hAgainst
            simp only [displayedAnswerSpeedInFeetPerSecond] at hAgainst
            change |v - 20| ≤ |v - 23| at hAgainst
            have hGap : (1 / 2 : ℝ) < v - 20 :=
              (by norm_num : (1 / 2 : ℝ) < 45 / 2 - 20).trans
                (sub_lt_sub_right hvLower 20)
            rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1 / 2).trans hGap)]
              at hAgainst
            exact False.elim
              (lt_irrefl _ ((hGap.trans_le hAgainst).trans hErrorBound))
        | C => rfl
        | D =>
            have hAgainst := hOther .C
            unfold displayedChoiceError at hAgainst
            simp only [displayedAnswerSpeedInFeetPerSecond] at hAgainst
            change |v - 26| ≤ |v - 23| at hAgainst
            have hGap : (1 / 2 : ℝ) < 26 - v :=
              (by norm_num : (1 / 2 : ℝ) < 26 - 47 / 2).trans
                (sub_lt_sub_left hvUpper 26)
            have hv26 : v < 26 :=
              hvUpper.trans (by norm_num)
            rw [abs_of_neg (sub_neg.mpr hv26)] at hAgainst
            have hAgainst' : 26 - v ≤ |v - 23| := by
              simpa only [neg_sub] using hAgainst
            exact False.elim
              (lt_irrefl _ ((hGap.trans_le hAgainst').trans hErrorBound))
      exact ⟨hDistance, hExactSpeed, hRounds, hMatchesC, hUniqueC⟩
  
end PhyXMiniProblems.ProblemPhyXMini0751
