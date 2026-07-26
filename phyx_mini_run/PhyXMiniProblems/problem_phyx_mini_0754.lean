import Mathlib.Analysis.Calculus.Deriv.Add
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0754

open Dimension

/-!
# Ball launched beside a constant-speed construction elevator

The primary figure places a ball and the floor of a construction cab at ground
level.  Its two velocity arrows, labelled `v₀` and `v_c`, point vertically
upward.  At the common start time the ball has speed `7.00 m/s`, while the cab
moves upward at the constant speed `3.00 m/s`.

The physical quantities below use Physlib's unit-independent
`Dimensionful (WithDim _ _)` representation.  Real-valued functions occur only
as signed vertical-component readouts in SI units: time in seconds, height in
metres, velocity in metres per second, and acceleration in metres per second
squared.  Positive readouts point upward.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- A signed physical position along the vertical axis. -/
abbrev VerticalPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed physical velocity along the vertical axis. -/
abbrev VerticalVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A physical acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a signed position in the length unit selected by `units`. -/
def verticalPositionReadout
    (units : UnitChoices) (position : VerticalPositionQuantity) : ℝ :=
  (position units).val

/-- Read a signed vertical velocity in the units selected by `units`. -/
def verticalVelocityReadout
    (units : UnitChoices) (velocity : VerticalVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Read a nonnegative acceleration magnitude in the units selected by `units`. -/
def accelerationMagnitudeReadout
    (units : UnitChoices) (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- Metre readout of a signed vertical position. -/
def verticalPositionInMeters (position : VerticalPositionQuantity) : ℝ :=
  verticalPositionReadout UnitChoices.SI position

/-- Metres-per-second readout of a signed vertical velocity. -/
def verticalVelocityInMetersPerSecond
    (velocity : VerticalVelocityQuantity) : ℝ :=
  verticalVelocityReadout UnitChoices.SI velocity

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationMagnitudeReadout UnitChoices.SI acceleration

/-! ## Primary-figure labels and geometry -/

/-- The two velocity arrows printed in the supplied bitmap. -/
inductive FigureVelocityArrow where
  | cabVc
  | ballV0
  deriving DecidableEq, Repr

/-- The objects whose initial locations are visible in the bitmap. -/
inductive FigureObject where
  | constructionCabFloor
  | ball
  deriving DecidableEq, Repr

/-- Orientation along the vertical axis. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Structured qualitative information read directly from the primary image. -/
structure ElevatorBallFigure where
  arrowDirection : FigureVelocityArrow → VerticalDirection
  startsAtGround : FigureObject → Prop
  objectLabel : FigureObject → String
  personShownInsideCab : Prop

/-! ## Physical setup and supplied data -/

/--
The trajectories and dimensionful parameters of the one-dimensional model.

The argument of each trajectory is an SI time readout in seconds.  The
relative-velocity trajectory is an independent physical quantity whose
governing relation to the ball and cab velocities is stated below; no field
assigns its derivative or the requested answer.
-/
structure ElevatorBallSetup where
  figure : ElevatorBallFigure
  launchTimeSeconds : ℝ
  ballHeight : ℝ → VerticalPositionQuantity
  cabFloorHeight : ℝ → VerticalPositionQuantity
  ballVerticalVelocity : ℝ → VerticalVelocityQuantity
  cabVerticalVelocity : ℝ → VerticalVelocityQuantity
  relativeVerticalVelocity : ℝ → VerticalVelocityQuantity
  ballInitialVerticalVelocity : VerticalVelocityQuantity
  cabConstantVerticalVelocity : VerticalVelocityQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity

/--
Numerical values and simultaneous ground-level start stated in the problem.
The initial velocity values are retained even though they cancel out of the
relative acceleration.
-/
structure MatchesProblemStatement (setup : ElevatorBallSetup) : Prop where
  commonStartTimeIsZero : setup.launchTimeSeconds = 0
  ballStartsAtGround :
    verticalPositionInMeters
        (setup.ballHeight setup.launchTimeSeconds) = 0
  cabFloorStartsAtGround :
    verticalPositionInMeters
        (setup.cabFloorHeight setup.launchTimeSeconds) = 0
  ballVelocityAtLaunch :
    setup.ballVerticalVelocity setup.launchTimeSeconds =
      setup.ballInitialVerticalVelocity
  ballInitialSpeedMetersPerSecond :
    verticalVelocityInMetersPerSecond
        setup.ballInitialVerticalVelocity = 7
  cabSpeedMetersPerSecond :
    verticalVelocityInMetersPerSecond
        setup.cabConstantVerticalVelocity = 3

/--
Readouts from the supplied bitmap: both velocity arrows point upward, both
objects begin on the ground line, the ball is labelled, and a person is drawn
inside the construction cab.
-/
structure MatchesPrimaryFigure (setup : ElevatorBallSetup) : Prop where
  ballInitialVelocityArrowPointsUp :
    setup.figure.arrowDirection .ballV0 = .upward
  cabVelocityArrowPointsUp :
    setup.figure.arrowDirection .cabVc = .upward
  ballShownAtGround : setup.figure.startsAtGround .ball
  cabFloorShownAtGround :
    setup.figure.startsAtGround .constructionCabFloor
  ballLabel : setup.figure.objectLabel .ball = "Ball"
  personInsideCab : setup.figure.personShownInsideCab

/--
The conventional near-Earth gravitational calibration used by the recorded
multiple-choice answer.
-/
def UsesStandardTerrestrialGravity (setup : ElevatorBallSetup) : Prop :=
  accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-- Positivity of the sole acceleration magnitude in the idealized model. -/
def HasPhysicalGravity (setup : ElevatorBallSetup) : Prop :=
  0 < accelerationMagnitudeInMetersPerSecondSquared
    setup.gravitationalAccelerationMagnitude

/-! ## Differential kinematics -/

/--
At an SI time readout, the derivative of a metre-valued height readout is the
corresponding metres-per-second velocity readout.
-/
def HasVerticalVelocityAt
    (position : ℝ → VerticalPositionQuantity)
    (velocity : VerticalVelocityQuantity)
    (timeSeconds : ℝ) : Prop :=
  HasDerivAt
    (fun t ↦ verticalPositionInMeters (position t))
    (verticalVelocityInMetersPerSecond velocity)
    timeSeconds

/--
At an SI time readout, the derivative of a metres-per-second velocity readout
has the given signed metres-per-second-squared value.
-/
def HasVerticalAccelerationReadoutAt
    (velocity : ℝ → VerticalVelocityQuantity)
    (signedAccelerationSI timeSeconds : ℝ) : Prop :=
  HasDerivAt
    (fun t ↦ verticalVelocityInMetersPerSecond (velocity t))
    signedAccelerationSI
    timeSeconds

/--
Governing laws for ideal free fall beside a constant-speed cab.

The ball accelerates downward with magnitude `g`; the cab velocity is constant;
and relative velocity is ball velocity minus cab-floor velocity in every
coherent unit system.  None of these fields gives the magnitude of the
relative acceleration or selects an answer choice.
-/
structure SatisfiesElevatorBallKinematics
    (setup : ElevatorBallSetup) : Prop where
  ballVelocityIsHeightDerivative :
    ∀ timeSeconds,
      HasVerticalVelocityAt setup.ballHeight
        (setup.ballVerticalVelocity timeSeconds) timeSeconds
  cabVelocityIsHeightDerivative :
    ∀ timeSeconds,
      HasVerticalVelocityAt setup.cabFloorHeight
        (setup.cabVerticalVelocity timeSeconds) timeSeconds
  ballFreeFallAcceleration :
    ∀ timeSeconds,
      HasVerticalAccelerationReadoutAt setup.ballVerticalVelocity
        (-accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude)
        timeSeconds
  cabMovesAtConstantVelocity :
    ∀ timeSeconds,
      setup.cabVerticalVelocity timeSeconds =
        setup.cabConstantVerticalVelocity
  relativeVelocityLaw :
    ∀ timeSeconds units,
      verticalVelocityReadout units
          (setup.relativeVerticalVelocity timeSeconds) =
        verticalVelocityReadout units
            (setup.ballVerticalVelocity timeSeconds) -
          verticalVelocityReadout units
            (setup.cabVerticalVelocity timeSeconds)

/-- A constant cab velocity has zero signed acceleration readout. -/
lemma cab_vertical_velocity_has_zero_derivative
    (setup : ElevatorBallSetup)
    (_laws : SatisfiesElevatorBallKinematics setup)
    (timeSeconds : ℝ) :
    HasVerticalAccelerationReadoutAt setup.cabVerticalVelocity 0
      timeSeconds := by
  simpa only [HasVerticalAccelerationReadoutAt,
    _laws.cabMovesAtConstantVelocity] using
    (hasDerivAt_const timeSeconds
      (verticalVelocityInMetersPerSecond
        setup.cabConstantVerticalVelocity))

/--
Subtracting the zero cab acceleration from the ball's downward free-fall
acceleration gives the signed derivative of the relative velocity.
-/
lemma relative_vertical_velocity_derivative
    (setup : ElevatorBallSetup)
    (_laws : SatisfiesElevatorBallKinematics setup)
    (timeSeconds : ℝ) :
    HasVerticalAccelerationReadoutAt setup.relativeVerticalVelocity
      (-accelerationMagnitudeInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude)
      timeSeconds := by
  have hball := _laws.ballFreeFallAcceleration timeSeconds
  have hcab :=
    cab_vertical_velocity_has_zero_derivative setup _laws timeSeconds
  unfold HasVerticalAccelerationReadoutAt at hball hcab ⊢
  have hrelative :
      (fun t ↦
        verticalVelocityInMetersPerSecond
          (setup.relativeVerticalVelocity t)) =
        (fun t ↦
          verticalVelocityInMetersPerSecond
              (setup.ballVerticalVelocity t) -
            verticalVelocityInMetersPerSecond
              (setup.cabVerticalVelocity t)) := by
    funext t
    simpa only [verticalVelocityInMetersPerSecond] using
      _laws.relativeVelocityLaw t UnitChoices.SI
  rw [hrelative]
  simpa only [Pi.sub_def, sub_zero] using hball.sub hcab

/-! ## Requested rate and displayed answers -/

/--
The magnitude of the signed derivative of the ball's velocity relative to the
cab floor.  This is the relative-acceleration magnitude meant by the source's
phrase "rate does the speed ... change relative to the cab floor."
-/
def RelativeVelocityChangesAtRateMagnitudeAt
    (setup : ElevatorBallSetup)
    (rateMagnitudeMetersPerSecondSquared timeSeconds : ℝ) : Prop :=
  ∃ signedRateMetersPerSecondSquared : ℝ,
    HasVerticalAccelerationReadoutAt setup.relativeVerticalVelocity
        signedRateMetersPerSecondSquared timeSeconds ∧
      |signedRateMetersPerSecondSquared| =
        rateMagnitudeMetersPerSecondSquared

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Exact SI acceleration readouts represented by the printed decimals. -/
def answerChoiceAccelerationInMetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 46 / 5
  | .B => 19 / 2
  | .C => 49 / 5
  | .D => 101 / 10

/-- The answer label recorded in the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Because a constant-velocity cab has zero acceleration, subtracting its motion
does not change the ball's acceleration.  Thus the derivative of relative
vertical velocity is `-9.80 m/s²`, and its magnitude is choice `C`,
`9.80 m/s²`.

This formalizes blueprint label `thm:physics:phyx_mini_0754:target`.
-/
theorem problem_phyx_mini_0754
    (setup : ElevatorBallSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalGravity setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_laws : SatisfiesElevatorBallKinematics setup) :
    ∀ timeSeconds,
      RelativeVelocityChangesAtRateMagnitudeAt setup
        (answerChoiceAccelerationInMetersPerSecondSquared .C)
        timeSeconds := by
  intro timeSeconds
  refine ⟨
    -accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude,
    relative_vertical_velocity_derivative setup _laws timeSeconds,
    ?_⟩
  have hpos :
      0 < accelerationMagnitudeInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude := _physical
  rw [abs_neg, abs_of_pos hpos]
  simpa only [UsesStandardTerrestrialGravity,
    answerChoiceAccelerationInMetersPerSecondSquared] using _gravity

end PhyXMiniProblems.ProblemPhyXMini0754
