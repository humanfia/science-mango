import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0747

open Dimension

/-!
# Baseball crossing a wall top twice

A baseball is hit at height `h = 1.00 m` and is later caught at the same
height.  Its no-drag trajectory crosses the horizontal top of a wall on the
way up at `1.00 s` and crosses it again on the way down `4.00 s` later.  The
two crossing points are separated by `D = 50.0 m` along the wall.  The
question asks for the wall height.

Basic physical scalars are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` quantities.  Real numbers occur only as named SI
readouts of those quantities and as schematic or multiple-choice data.

Assumption/target split:

* `SatisfiesIdealProjectileLaws` contains the general constant-gravity
  position and velocity equations;
* `MatchesProblemStatement` contains the supplied times, distances, and
  crossing/catching incidences;
* `MatchesPrimaryFigure` transcribes only the two `h` labels, the `D` label,
  the brick wall, and the dashed parabolic arc;
* `UsesStandardNearEarthGravity` supplies the textbook value `9.8 m/s^2`;
* there are no previous-part results; and
* the requested `25.5 m` wall height occurs only in the final theorem and in
  the displayed-answer table.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- The physical dimension of velocity, `L T^-1`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed Cartesian position component with the dimension of length. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed Cartesian velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian position component in SI metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical elapsed time in SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a signed Cartesian velocity component in SI metres per second. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read an acceleration magnitude in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure vocabulary -/

/-- The type of moving object named in the problem. -/
inductive ProjectileKind where
  | baseball
  deriving DecidableEq, Repr

/-- The idealized mechanics model used after the hit. -/
inductive ProjectileModel where
  | constantGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- The hit and catch endpoints whose common height is labelled `h`. -/
inductive HeightEndpoint where
  | hit
  | catch
  deriving DecidableEq, Fintype, Repr

/-- The two intersections of the dashed trajectory with the wall top. -/
inductive WallTopCrossing where
  | ascending
  | descending
  deriving DecidableEq, Fintype, Repr

/-- Literal mathematical labels visible in image `747.png`. -/
inductive FigureLabel where
  | h
  | D
  deriving DecidableEq, Fintype, Repr

/-- Physical or graphical objects visibly represented in the primary image. -/
inductive FigureObject where
  | brickWall
  | groundLine
  | dashedParabolicTrajectory
  deriving DecidableEq, Fintype, Repr

/-- Schematic anchors used as endpoints of the three dimension arrows. -/
inductive FigureAnchor where
  | groundBelowHit
  | hitPoint
  | ascendingWallTopPoint
  | descendingWallTopPoint
  | catchPoint
  | groundBelowCatch
  deriving DecidableEq, Fintype, Repr

/-- A planar physical position with signed horizontal and vertical components. -/
structure PlanarPosition where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- A planar physical velocity with signed horizontal and vertical components. -/
structure PlanarVelocity where
  horizontal : SignedVelocityQuantity
  vertical : SignedVelocityQuantity

/-!
The labels, dimension-arrow endpoints, and qualitative geometry read directly
from the supplied bitmap.  The marked quantities are independent physical
lengths; the figure does not assign a numerical value to the wall height.
-/
structure BaseballWallFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  markedEndpointHeight : HeightEndpoint → LengthQuantity
  markedCrossingSeparation : LengthQuantity
  heightArrowEndpoints : HeightEndpoint → FigureAnchor × FigureAnchor
  distanceArrowEndpoints : FigureAnchor × FigureAnchor
  trajectoryMeetsWallTopAt : WallTopCrossing → Bool
  wallTopDrawnHorizontal : Bool
  hitAndCatchDrawnAtSameHeight : Bool

/-! ## Independent physical setup -/

/-!
All physical quantities and observables in the experiment.  The wall height
is an independent field, not a definition of the requested answer.  The
position and velocity functions are constrained only by the governing laws
below.
-/
structure BaseballWallSetup where
  projectileKind : ProjectileKind
  model : ProjectileModel
  initialHeight : LengthQuantity
  wallHeight : LengthQuantity
  distanceAlongWallBetweenCrossings : LengthQuantity
  hitTime : TimeQuantity
  ascendingWallTopTime : TimeQuantity
  timeBetweenWallTopCrossings : TimeQuantity
  descendingWallTopTime : TimeQuantity
  catchTime : TimeQuantity
  initialHorizontalVelocity : SignedVelocityQuantity
  initialVerticalVelocity : SignedVelocityQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  positionAt : TimeQuantity → PlanarPosition
  velocityAt : TimeQuantity → PlanarVelocity
  figure : BaseballWallFigure

/-! ## Problem data, figure readouts, and physical assumptions -/

/-!
Numerical and incidence information supplied by the prose.  In particular,
the two trajectory values at the crossing times are equated to the independent
wall-height field, but that field is not assigned the requested numerical
answer here.
-/
structure MatchesProblemStatement (setup : BaseballWallSetup) : Prop where
  projectileIsBaseball : setup.projectileKind = .baseball
  usesIdealProjectileModel :
    setup.model = .constantGravityNegligibleDrag
  hitOccursAtZeroSeconds : timeInSeconds setup.hitTime = 0
  initialHeightMeters : lengthInMeters setup.initialHeight = 1
  ascendingCrossingTimeSeconds :
    timeInSeconds setup.ascendingWallTopTime = 1
  crossingTimeGapSeconds :
    timeInSeconds setup.timeBetweenWallTopCrossings = 4
  descendingTimeIsFourSecondsLater :
    timeInSeconds setup.descendingWallTopTime =
      timeInSeconds setup.ascendingWallTopTime +
        timeInSeconds setup.timeBetweenWallTopCrossings
  crossingSeparationMeters :
    lengthInMeters setup.distanceAlongWallBetweenCrossings = 50
  hitAtInitialHeight :
    signedLengthInMeters (setup.positionAt setup.hitTime).vertical =
      lengthInMeters setup.initialHeight
  caughtAtSameHeight :
    signedLengthInMeters (setup.positionAt setup.catchTime).vertical =
      lengthInMeters setup.initialHeight
  ascendingCrossingIsAtWallTop :
    signedLengthInMeters
        (setup.positionAt setup.ascendingWallTopTime).vertical =
      lengthInMeters setup.wallHeight
  descendingCrossingIsAtWallTop :
    signedLengthInMeters
        (setup.positionAt setup.descendingWallTopTime).vertical =
      lengthInMeters setup.wallHeight
  crossingDistanceIsAlongWall :
    signedLengthInMeters
          (setup.positionAt setup.descendingWallTopTime).horizontal -
        signedLengthInMeters
          (setup.positionAt setup.ascendingWallTopTime).horizontal =
      lengthInMeters setup.distanceAlongWallBetweenCrossings

/-!
Literal and qualitative evidence from image `747.png`.  These fields connect
the repeated `h` label to the common hit/catch height and the `D` label to the
distance between wall-top crossings, without asserting the wall's height.
-/
structure MatchesPrimaryFigure (setup : BaseballWallSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  hitHeightLabelMatches :
    setup.figure.markedEndpointHeight .hit = setup.initialHeight
  catchHeightLabelMatches :
    setup.figure.markedEndpointHeight .catch = setup.initialHeight
  distanceLabelMatches :
    setup.figure.markedCrossingSeparation =
      setup.distanceAlongWallBetweenCrossings
  hitHeightArrowEndpoints :
    setup.figure.heightArrowEndpoints .hit =
      (.groundBelowHit, .hitPoint)
  catchHeightArrowEndpoints :
    setup.figure.heightArrowEndpoints .catch =
      (.groundBelowCatch, .catchPoint)
  distanceArrowEndpoints :
    setup.figure.distanceArrowEndpoints =
      (.ascendingWallTopPoint, .descendingWallTopPoint)
  bothWallTopCrossingsShown :
    ∀ crossing, setup.figure.trajectoryMeetsWallTopAt crossing = true
  horizontalWallTop : setup.figure.wallTopDrawnHorizontal = true
  equalEndpointHeights : setup.figure.hitAndCatchDrawnAtSameHeight = true

/-!
The standard near-Earth gravitational acceleration implicit in the recorded
numerical answer.  This calibration contains no wall-height information.
-/
structure UsesStandardNearEarthGravity (setup : BaseballWallSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-!
Positivity, chronological order, and the ascending/descending branches named
in the prose.  These select the physical trajectory without fixing the wall
height to any displayed answer.
-/
structure HasPhysicalProjectileParameters (setup : BaseballWallSetup) : Prop where
  initialHeightPositive : 0 < lengthInMeters setup.initialHeight
  wallAboveHitHeight :
    lengthInMeters setup.initialHeight < lengthInMeters setup.wallHeight
  crossingSeparationPositive :
    0 < lengthInMeters setup.distanceAlongWallBetweenCrossings
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  hitBeforeAscendingCrossing :
    timeInSeconds setup.hitTime < timeInSeconds setup.ascendingWallTopTime
  ascendingBeforeDescendingCrossing :
    timeInSeconds setup.ascendingWallTopTime <
      timeInSeconds setup.descendingWallTopTime
  descendingCrossingBeforeCatch :
    timeInSeconds setup.descendingWallTopTime < timeInSeconds setup.catchTime
  crossingGapPositive :
    0 < timeInSeconds setup.timeBetweenWallTopCrossings
  movesForwardAlongWall :
    0 < signedVelocityInMetersPerSecond
      setup.initialHorizontalVelocity
  movingUpAtFirstCrossing :
    0 < signedVelocityInMetersPerSecond
      (setup.velocityAt setup.ascendingWallTopTime).vertical
  movingDownAtSecondCrossing :
    signedVelocityInMetersPerSecond
      (setup.velocityAt setup.descendingWallTopTime).vertical < 0

/-!
Ideal no-drag projectile kinematics in coherent SI readouts.  Time is elapsed
from the hit, the horizontal origin is the hit point, and upward is positive.
These general laws mention neither a wall-height answer nor an answer choice.
-/
structure SatisfiesIdealProjectileLaws (setup : BaseballWallSetup) : Prop where
  uniformHorizontalPosition : ∀ time : TimeQuantity,
    signedLengthInMeters (setup.positionAt time).horizontal =
      signedVelocityInMetersPerSecond setup.initialHorizontalVelocity *
        timeInSeconds time
  verticalConstantGravityPosition : ∀ time : TimeQuantity,
    signedLengthInMeters (setup.positionAt time).vertical =
      lengthInMeters setup.initialHeight +
        signedVelocityInMetersPerSecond setup.initialVerticalVelocity *
          timeInSeconds time -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          timeInSeconds time ^ 2
  uniformHorizontalVelocity : ∀ time : TimeQuantity,
    signedVelocityInMetersPerSecond (setup.velocityAt time).horizontal =
      signedVelocityInMetersPerSecond setup.initialHorizontalVelocity
  verticalConstantGravityVelocity : ∀ time : TimeQuantity,
    signedVelocityInMetersPerSecond (setup.velocityAt time).vertical =
      signedVelocityInMetersPerSecond setup.initialVerticalVelocity -
        accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          timeInSeconds time

/-! ## Multiple-choice display and target -/

/-- Labels of the four wall-height answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wall height in metres printed beside each displayed answer label. -/
def displayedWallHeightInMeters : AnswerChoice → ℝ
  | .A => 43 / 2
  | .B => 47 / 2
  | .C => 51 / 2
  | .D => 55 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A setup's wall-height readout agrees with a displayed answer. -/
def MatchesDisplayedWallHeight
    (setup : BaseballWallSetup) (choice : AnswerChoice) : Prop :=
  lengthInMeters setup.wallHeight = displayedWallHeightInMeters choice

/-!
The equal wall-top heights at `1 s` and `5 s` determine the initial vertical
velocity.  Substitution into the constant-gravity trajectory with
`h = 1 m` and `g = 9.8 m/s^2` gives a wall height of `25.5 m`, answer C.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0747:target`.
-/
theorem problem_phyx_mini_0747
    (setup : BaseballWallSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesIdealProjectileLaws setup) :
    lengthInMeters setup.wallHeight = 51 / 2 ∧
      MatchesDisplayedWallHeight setup .C := by
  have descendingTimeSeconds :
      timeInSeconds setup.descendingWallTopTime = 5 := by
    rw [_statement.descendingTimeIsFourSecondsLater,
      _statement.ascendingCrossingTimeSeconds,
      _statement.crossingTimeGapSeconds]
    norm_num
  have ascendingPosition :=
    _laws.verticalConstantGravityPosition setup.ascendingWallTopTime
  have descendingPosition :=
    _laws.verticalConstantGravityPosition setup.descendingWallTopTime
  rw [_statement.ascendingCrossingIsAtWallTop,
    _statement.initialHeightMeters,
    _statement.ascendingCrossingTimeSeconds,
    _gravity.gravityMetersPerSecondSquared] at ascendingPosition
  rw [_statement.descendingCrossingIsAtWallTop,
    _statement.initialHeightMeters,
    descendingTimeSeconds,
    _gravity.gravityMetersPerSecondSquared] at descendingPosition
  have wallHeightMeters :
      lengthInMeters setup.wallHeight = 51 / 2 := by
    nlinarith [ascendingPosition, descendingPosition]
  exact ⟨wallHeightMeters, by
    simpa [MatchesDisplayedWallHeight, displayedWallHeightInMeters]
      using wallHeightMeters⟩

end PhyXMiniProblems.ProblemPhyXMini0747
