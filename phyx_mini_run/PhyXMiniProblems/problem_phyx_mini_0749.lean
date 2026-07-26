import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0749

open Dimension

/-!
# Vertical launch velocity from a sled-displacement graph

A sled moves at constant speed in the negative `x` direction.  A ball is
launched from it with sled-frame velocity components `v0x` and `v0y`.  The
primary figure plots the ball's ground-frame horizontal displacement against
the positive magnitude `v_s` of the sled's leftward velocity.  Its straight
line passes through `(0, 40)`, `(10, 0)`, and `(20, -40)` when the axes are
read in metres per second and metres.

Lengths, durations, signed velocity components, acceleration magnitudes, and
speeds below are unit-independent Physlib quantities.  Real numbers occur
only at explicitly coherent-SI readout boundaries, in schematic coordinates,
and as the printed multiple-choice values.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed physical length or one-dimensional position. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional physical velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A nonnegative magnitude of physical acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Metre readout of a signed physical length. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Second readout of a nonnegative physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a signed physical velocity component. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Metre-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- The physical speed having the specified nonnegative SI readout. -/
def speedFromMetersPerSecond (value : NNReal) : DimSpeed :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- The three sled-speed values at which the graph supplies exact points. -/
def graphSledSpeedZero : DimSpeed := speedFromMetersPerSecond 0
def graphSledSpeedTen : DimSpeed := speedFromMetersPerSecond 10
def graphSledSpeedTwenty : DimSpeed := speedFromMetersPerSecond 20

/-! ## Physical roles and literal primary-figure vocabulary -/

/-- Directed orientations used by the coordinate axes and velocity arrow. -/
inductive ArrowDirection where
  | left
  | right
  | up
  | down
  deriving DecidableEq, Repr

/-- Objects explicitly labelled in the left-hand sled diagram. -/
inductive FigureObject where
  | sled
  | ball
  deriving DecidableEq, Fintype, Repr

/-- Quantity labels visible in either panel of the supplied image. -/
inductive FigureQuantityLabel where
  | xAxis
  | yAxis
  | sledSpeed_vs
  | groundDisplacement_deltaXbg
  deriving DecidableEq, Fintype, Repr

/-- Physical quantities assigned to the two axes of the right-hand graph. -/
inductive GraphAxisQuantity where
  | sledSpeed
  | ballGroundHorizontalDisplacement
  deriving DecidableEq, Repr

/-!
Literal diagram and graph information from image `749.png`.  Schematic object
coordinates express only the relative layout of the drawing; measured
kinematic quantities remain in the dimensionful setup below.
-/
structure SledProjectileFigure where
  objectHorizontalCoordinate : FigureObject → ℝ
  objectVerticalCoordinate : FigureObject → ℝ
  positiveXAxisDirection : ArrowDirection
  positiveYAxisDirection : ArrowDirection
  sledVelocityArrowDirection : ArrowDirection
  showsObjectLabel : FigureObject → Bool
  showsQuantityLabel : FigureQuantityLabel → Bool
  graphHorizontalAxisQuantity : GraphAxisQuantity
  graphVerticalAxisQuantity : GraphAxisQuantity
  graphSpeedLengthUnit : LengthUnit
  graphSpeedTimeUnit : TimeUnit
  graphDisplacementLengthUnit : LengthUnit
  horizontalTickShown : ℝ → Bool
  verticalTickShown : ℝ → Bool
  straightLineShown : Bool

/-!
Independent physical quantities in the family of launch experiments shown by
the graph.  The parameter of each function is the nonnegative speed magnitude
`v_s`; the corresponding sled velocity component is negative.  In particular,
the requested vertical launch component is an independent field and is not
defined from the recorded answer.
-/
structure SledProjectileSetup where
  figure : SledProjectileFigure
  launchVelocityRelativeToSledX : SignedVelocityQuantity
  launchVelocityRelativeToSledY : SignedVelocityQuantity
  flightDuration : DurationQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  launchHeightAboveDatum : SignedLengthQuantity
  landingHeightAboveDatum : SignedLengthQuantity
  sledGroundVelocityX : DimSpeed → SignedVelocityQuantity
  ballGroundVelocityX : DimSpeed → SignedVelocityQuantity
  ballGroundHorizontalDisplacement : DimSpeed → SignedLengthQuantity

/-! ## Figure data, scenario assumptions, and governing laws -/

/-!
Primary-image evidence.  Besides the coordinate directions, object labels,
and units, it records the three collinear graph points
`(0, 40)`, `(10, 0)`, and `(20, -40)`.  These are measured inputs, not the
requested value of `v0y`.
-/
structure MatchesPrimaryFigure (setup : SledProjectileSetup) : Prop where
  ballDrawnAboveSled :
    setup.figure.objectVerticalCoordinate .sled <
      setup.figure.objectVerticalCoordinate .ball
  positiveXAxisPointsRight : setup.figure.positiveXAxisDirection = .right
  positiveYAxisPointsUp : setup.figure.positiveYAxisDirection = .up
  sledVelocityArrowPointsLeft :
    setup.figure.sledVelocityArrowDirection = .left
  everyObjectLabelIsShown :
    ∀ object, setup.figure.showsObjectLabel object = true
  everyQuantityLabelIsShown :
    ∀ label, setup.figure.showsQuantityLabel label = true
  horizontalAxisIsSledSpeed :
    setup.figure.graphHorizontalAxisQuantity = .sledSpeed
  verticalAxisIsGroundDisplacement :
    setup.figure.graphVerticalAxisQuantity =
      .ballGroundHorizontalDisplacement
  speedAxisUsesMetersPerSecond :
    setup.figure.graphSpeedLengthUnit = LengthUnit.meters ∧
      setup.figure.graphSpeedTimeUnit = TimeUnit.seconds
  displacementAxisUsesMeters :
    setup.figure.graphDisplacementLengthUnit = LengthUnit.meters
  printedHorizontalTicksShown :
    setup.figure.horizontalTickShown 10 = true ∧
      setup.figure.horizontalTickShown 20 = true
  printedVerticalTicksShown :
    setup.figure.verticalTickShown (-40) = true ∧
      setup.figure.verticalTickShown 0 = true ∧
        setup.figure.verticalTickShown 40 = true
  graphIsStraight : setup.figure.straightLineShown = true
  displacementAtZeroSpeedMeters :
    signedLengthInMeters
        (setup.ballGroundHorizontalDisplacement graphSledSpeedZero) = 40
  displacementAtTenMetersPerSecond :
    signedLengthInMeters
        (setup.ballGroundHorizontalDisplacement graphSledSpeedTen) = 0
  displacementAtTwentyMetersPerSecond :
    signedLengthInMeters
        (setup.ballGroundHorizontalDisplacement graphSledSpeedTwenty) = -40

/-!
The prose specifies a level launch-and-landing experiment and identifies the
two stored launch-velocity components as components relative to the sled.
Equal endpoint heights is scenario data; it does not prescribe either the
flight duration or the requested vertical velocity.
-/
structure MatchesProblemDescription (setup : SledProjectileSetup) : Prop where
  landsAtLaunchHeight :
    setup.landingHeightAboveDatum = setup.launchHeightAboveDatum

/-- Standard near-Earth gravitational acceleration used by the ideal model. -/
structure UsesStandardNearEarthGravity
    (setup : SledProjectileSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 9.80

/-- Positivity conditions selecting the nondegenerate physical flight. -/
structure HasPhysicalSledProjectileParameters
    (setup : SledProjectileSetup) : Prop where
  flightDurationPositive : 0 < durationInSeconds setup.flightDuration
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude

/-!
Ideal no-drag kinematics for every plotted value of `v_s`:

* the sled's ground-frame `x` velocity is `-v_s`;
* Galilean velocity addition gives the ball's ground-frame `x` velocity;
* horizontal displacement is that constant velocity times the common flight
  duration; and
* vertical displacement under uniform downward gravity is
  `v0y * T - g * T^2 / 2`.

These are general physical laws and contain neither the numerical value of
`v0y` nor an answer-choice assertion.
-/
structure SatisfiesIdealSledProjectileLaws
    (setup : SledProjectileSetup) : Prop where
  sledMovesLeftAtSpecifiedSpeed : ∀ sledSpeed,
    signedVelocityInMetersPerSecond
        (setup.sledGroundVelocityX sledSpeed) =
      -speedInMetersPerSecond sledSpeed
  galileanHorizontalVelocityAddition : ∀ sledSpeed,
    signedVelocityInMetersPerSecond
        (setup.ballGroundVelocityX sledSpeed) =
      signedVelocityInMetersPerSecond
          setup.launchVelocityRelativeToSledX +
        signedVelocityInMetersPerSecond
          (setup.sledGroundVelocityX sledSpeed)
  uniformHorizontalMotion : ∀ sledSpeed,
    signedLengthInMeters
        (setup.ballGroundHorizontalDisplacement sledSpeed) =
      signedVelocityInMetersPerSecond
          (setup.ballGroundVelocityX sledSpeed) *
        durationInSeconds setup.flightDuration
  uniformGravityVerticalMotion :
    signedLengthInMeters setup.landingHeightAboveDatum -
        signedLengthInMeters setup.launchHeightAboveDatum =
      signedVelocityInMetersPerSecond
          setup.launchVelocityRelativeToSledY *
          durationInSeconds setup.flightDuration -
        accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          durationInSeconds setup.flightDuration ^ 2 / 2

/-! ## Derived kinematics and displayed answer -/

/-!
The graph's horizontal intercept and vertical intercept, together with
Galilean horizontal motion, determine `v0x = 10 m/s` and a `4 s` flight.
Neither result is included in a premise structure.
-/
lemma graphDeterminesHorizontalLaunchVelocityAndFlightDuration
    (setup : SledProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalSledProjectileParameters setup)
    (_laws : SatisfiesIdealSledProjectileLaws setup) :
    signedVelocityInMetersPerSecond
          setup.launchVelocityRelativeToSledX = 10 ∧
      durationInSeconds setup.flightDuration = 4 := by
  have hT := _physical.flightDurationPositive
  have hZero := _figure.displacementAtZeroSpeedMeters
  have hTen := _figure.displacementAtTenMetersPerSecond
  have hSledZero :=
    _laws.sledMovesLeftAtSpecifiedSpeed graphSledSpeedZero
  have hSledTen :=
    _laws.sledMovesLeftAtSpecifiedSpeed graphSledSpeedTen
  have hBallZero :=
    _laws.galileanHorizontalVelocityAddition graphSledSpeedZero
  have hBallTen :=
    _laws.galileanHorizontalVelocityAddition graphSledSpeedTen
  have hMotionZero := _laws.uniformHorizontalMotion graphSledSpeedZero
  have hMotionTen := _laws.uniformHorizontalMotion graphSledSpeedTen
  simp [graphSledSpeedZero, graphSledSpeedTen, speedFromMetersPerSecond,
    speedInMetersPerSecond, CarriesDimension.toDimensionful_apply_apply]
    at hZero hTen hSledZero hSledTen hBallZero hBallTen hMotionZero hMotionTen
  constructor <;> nlinarith

/-!
Equal launch and landing heights give `0 = v0y T - g T²/2`; using the derived
`T = 4 s` and `g = 9.80 m/s²` yields `v0y = 19.6 m/s`.
-/
lemma verticalLaunchVelocityInMetersPerSecond_eq_19_6
    (setup : SledProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalSledProjectileParameters setup)
    (_laws : SatisfiesIdealSledProjectileLaws setup) :
    signedVelocityInMetersPerSecond
      setup.launchVelocityRelativeToSledY = 19.6 := by
  have hDuration :=
    (graphDeterminesHorizontalLaunchVelocityAndFlightDuration
      setup _figure _physical _laws).2
  have hHeight :=
    congrArg signedLengthInMeters _description.landsAtLaunchHeight
  have hMotion := _laws.uniformGravityVerticalMotion
  rw [hHeight, hDuration, _gravity.gravityMetersPerSecondSquared] at hMotion
  norm_num at hMotion ⊢
  nlinarith

/-- Labels of the four speed values printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Vertical-speed readout in metres per second printed beside each choice. -/
def AnswerChoice.verticalSpeedMetersPerSecond : AnswerChoice → ℝ
  | .A => 18.6
  | .B => 19.2
  | .C => 19.6
  | .D => 20.2

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The modeled vertical launch component equals the value printed by `choice`. -/
def MatchesDisplayedVerticalSpeed
    (setup : SledProjectileSetup) (choice : AnswerChoice) : Prop :=
  signedVelocityInMetersPerSecond
      setup.launchVelocityRelativeToSledY =
    choice.verticalSpeedMetersPerSecond

/-- A displayed value is strictly closer to the modeled readout than every alternative. -/
def IsUniqueClosestVerticalSpeedChoice
    (setup : SledProjectileSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |signedVelocityInMetersPerSecond
        setup.launchVelocityRelativeToSledY -
          choice.verticalSpeedMetersPerSecond| <
      |signedVelocityInMetersPerSecond
        setup.launchVelocityRelativeToSledY -
          other.verticalSpeedMetersPerSecond|

/-!
The ball's sled-frame vertical launch component is `19.6 m/s`, the value
printed for answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0749:target`.
-/
theorem problem_phyx_mini_0749
    (setup : SledProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalSledProjectileParameters setup)
    (_laws : SatisfiesIdealSledProjectileLaws setup) :
    signedVelocityInMetersPerSecond
          setup.launchVelocityRelativeToSledY = 19.6 ∧
      MatchesDisplayedVerticalSpeed setup .C ∧
      IsUniqueClosestVerticalSpeedChoice setup .C := by
  have hv :=
    verticalLaunchVelocityInMetersPerSecond_eq_19_6
      setup _figure _description _gravity _physical _laws
  refine ⟨hv, ?_, ?_⟩
  · simpa [MatchesDisplayedVerticalSpeed,
      AnswerChoice.verticalSpeedMetersPerSecond] using hv
  · rw [IsUniqueClosestVerticalSpeedChoice, hv]
    intro other hne
    cases other
    · norm_num [AnswerChoice.verticalSpeedMetersPerSecond]
    · norm_num [AnswerChoice.verticalSpeedMetersPerSecond]
    · contradiction
    · norm_num [AnswerChoice.verticalSpeedMetersPerSecond]

end PhyXMiniProblems.ProblemPhyXMini0749
