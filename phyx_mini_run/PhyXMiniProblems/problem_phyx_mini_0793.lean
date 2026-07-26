import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0793

open Dimension

/-!
# Position of an accelerating motorcyclist

The city-limits sign is the origin of a one-dimensional east-positive axis.
At `t = 0 s` the motorcyclist is at `x₀ = 5.0 m`, moving east at
`v₀x = 15 m/s`, and thereafter has the constant eastward acceleration
`aₓ = 4.0 m/s²`.  The question asks for his position when his speed is
`25 m/s`.

The primary bitmap also shows a separate later snapshot at `t = 2.0 s`, with
both `x` and `vₓ` marked unknown.  This depicted time is retained below as
figure evidence; it is not identified with the queried `25 m/s` event.

Positions, times, signed velocity components, speed magnitudes, and signed
accelerations are represented by unit-independent Physlib quantities.  Real
numbers occur only as coherent unit readouts or literal figure/answer data.

Assumption/target split:

* governing laws: the general one-dimensional constant-acceleration velocity
  and position equations, together with speed being the magnitude of signed
  velocity;
* previous-part results: none;
* problem and figure readouts: the signpost origin, east-positive axis,
  `x₀ = 5.0 m`, `t₀ = 0 s`, `v₀x = 15 m/s`, `aₓ = 4.0 m/s²`, the queried
  speed `25 m/s`, the two motorcycles, the `OSAGE` sign, and the separate
  unknown snapshot at `t = 2.0 s`;
* current target conclusions: the query event is `2.5 s` after the initial
  event, its position is `55 m` east of the signpost, and displayed choice B
  is the unique matching answer.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A signed position on the east-positive x-axis. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A signed one-dimensional velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A signed one-dimensional acceleration component. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a signed position in the length unit selected by coherent units. -/
def positionReadout
    (units : UnitChoices) (position : SignedPositionQuantity) : ℝ :=
  (position units).val

/-- Read a physical time in the time unit selected by coherent units. -/
def timeReadout (units : UnitChoices) (time : TimeQuantity) : ℝ :=
  (time units).val

/-- Read a signed velocity in the speed unit induced by coherent units. -/
def velocityReadout
    (units : UnitChoices) (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Read a speed magnitude in the speed unit induced by coherent units. -/
def speedReadout (units : UnitChoices) (speed : SpeedQuantity) : ℝ :=
  ((speed units).val : ℝ)

/-- Read a signed acceleration in the units induced by coherent units. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration units).val

/-- SI metre readout of a signed position. -/
def positionInMeters (position : SignedPositionQuantity) : ℝ :=
  positionReadout UnitChoices.SI position

/-- SI second readout of a physical time coordinate. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout UnitChoices.SI time

/-- SI metre-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout UnitChoices.SI velocity

/-- SI metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout UnitChoices.SI speed

/-- SI metre-per-second-squared readout of a signed acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  accelerationReadout UnitChoices.SI acceleration

/-! ## Physical motion and primary-image vocabulary -/

/-- Cardinal directions used to interpret the horizontal axis and arrows. -/
inductive CardinalDirection where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Fintype, Repr

/-- Distinct objects visible in the supplied raster. -/
inductive FigureObject where
  | cityLimitsSignpost
  | initialMotorcycle
  | laterMotorcycle
  | horizontalAxis
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in the supplied raster. -/
inductive FigureLabel where
  | cityNameOsage
  | originO
  | axisXEast
  | initialPositionX0
  | initialTime
  | initialVelocityV0x
  | accelerationAx
  | laterPositionX
  | laterTime
  | laterVelocityVx
  deriving DecidableEq, Fintype, Repr

/-!
Typed transcription of the primary bitmap.  The later position and velocity
remain independent dimensionful quantities even though the image marks their
scalar values with question marks.
-/
structure SuppliedMotorcycleFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  citySignText : String
  horizontalAxisText : String
  positiveAxisDirection : CardinalDirection
  originObject : FigureObject
  initialSceneObject : FigureObject
  laterSceneObject : FigureObject
  initialPositionLabel : SignedPositionQuantity
  initialTimeLabel : TimeQuantity
  initialVelocityArrow : SignedVelocityQuantity
  accelerationArrow : SignedAccelerationQuantity
  laterPositionLabel : SignedPositionQuantity
  laterTimeLabel : TimeQuantity
  laterVelocityArrow : SignedVelocityQuantity
  laterPositionMarkedUnknown : Bool
  laterVelocityMarkedUnknown : Bool

/-!
The independent physical trajectory and the event selected by the question.
In particular, `queryTime` and the position at that time are not defined from
the recorded answer.
-/
structure MotorcycleMotionSetup where
  cityLimitsSignPosition : SignedPositionQuantity
  initialTime : TimeQuantity
  queryTime : TimeQuantity
  position : TimeQuantity → SignedPositionQuantity
  velocity : TimeQuantity → SignedVelocityQuantity
  speed : TimeQuantity → SpeedQuantity
  constantAcceleration : SignedAccelerationQuantity
  figure : SuppliedMotorcycleFigure

/-! ## Stated data and primary-image evidence -/

/-!
Numerical data from the prose, including the condition selecting the event in
the question.  No queried position or answer label occurs here.
-/
structure MatchesProblemStatement (setup : MotorcycleMotionSetup) : Prop where
  cityLimitsSignIsOrigin :
    positionInMeters setup.cityLimitsSignPosition = 0
  initialTimeSeconds :
    timeInSeconds setup.initialTime = 0
  initialPositionMeters :
    positionInMeters (setup.position setup.initialTime) = 5
  initialVelocityMetersPerSecond :
    velocityInMetersPerSecond (setup.velocity setup.initialTime) = 15
  accelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.constantAcceleration = 4
  queriedSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.speed setup.queryTime) = 25

/-!
Literal objects, labels, orientations, and numerical annotations read from
image `793.png`.  The `2.0 s` image snapshot is tied to the same trajectory but
is deliberately not equated with `queryTime`.
-/
structure MatchesSuppliedMotorcycleFigure
    (setup : MotorcycleMotionSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  signReadsOsage : setup.figure.citySignText = "OSAGE"
  horizontalAxisReadsXEast : setup.figure.horizontalAxisText = "x (east)"
  eastIsPositive : setup.figure.positiveAxisDirection = .east
  originIsAtSignpost : setup.figure.originObject = .cityLimitsSignpost
  initialSceneIsFirstMotorcycle :
    setup.figure.initialSceneObject = .initialMotorcycle
  laterSceneIsSecondMotorcycle :
    setup.figure.laterSceneObject = .laterMotorcycle
  initialPositionLabelMatchesTrajectory :
    setup.figure.initialPositionLabel = setup.position setup.initialTime
  initialTimeLabelMatchesSetup :
    setup.figure.initialTimeLabel = setup.initialTime
  initialVelocityArrowMatchesTrajectory :
    setup.figure.initialVelocityArrow = setup.velocity setup.initialTime
  accelerationArrowMatchesMotion :
    setup.figure.accelerationArrow = setup.constantAcceleration
  initialPositionLabelMeters :
    positionInMeters setup.figure.initialPositionLabel = 5
  initialTimeLabelSeconds :
    timeInSeconds setup.figure.initialTimeLabel = 0
  initialVelocityArrowMetersPerSecond :
    velocityInMetersPerSecond setup.figure.initialVelocityArrow = 15
  accelerationArrowMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.figure.accelerationArrow = 4
  laterTimeLabelSeconds :
    timeInSeconds setup.figure.laterTimeLabel = 2
  laterPositionLabelMatchesTrajectory :
    setup.figure.laterPositionLabel = setup.position setup.figure.laterTimeLabel
  laterVelocityArrowMatchesTrajectory :
    setup.figure.laterVelocityArrow = setup.velocity setup.figure.laterTimeLabel
  laterPositionHasQuestionMark :
    setup.figure.laterPositionMarkedUnknown = true
  laterVelocityHasQuestionMark :
    setup.figure.laterVelocityMarkedUnknown = true

/-!
Direction and temporal facts selecting the physical future event.  These facts
contain neither its position nor a displayed answer value.
-/
structure HasPhysicalEastwardQueryEvent
    (setup : MotorcycleMotionSetup) : Prop where
  queryOccursAfterInitialTime :
    timeInSeconds setup.initialTime < timeInSeconds setup.queryTime
  initialVelocityPointsEast :
    0 < velocityInMetersPerSecond (setup.velocity setup.initialTime)
  queryVelocityPointsEast :
    0 < velocityInMetersPerSecond (setup.velocity setup.queryTime)
  accelerationPointsEast :
    0 < accelerationInMetersPerSecondSquared setup.constantAcceleration

/-! ## Governing constant-acceleration laws -/

/-!
Standard one-dimensional constant-acceleration kinematics, stated in every
coherent choice of units and relative to the initial event.  This interface
contains no value for the queried position, no `55 m`, and no answer label.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : MotorcycleMotionSetup) : Prop where
  velocityEvolution : ∀ units time,
    velocityReadout units (setup.velocity time) =
      velocityReadout units (setup.velocity setup.initialTime) +
        accelerationReadout units setup.constantAcceleration *
          (timeReadout units time - timeReadout units setup.initialTime)
  positionEvolution : ∀ units time,
    positionReadout units (setup.position time) =
      positionReadout units (setup.position setup.initialTime) +
        velocityReadout units (setup.velocity setup.initialTime) *
          (timeReadout units time - timeReadout units setup.initialTime) +
        (1 / 2 : ℝ) * accelerationReadout units setup.constantAcceleration *
          (timeReadout units time - timeReadout units setup.initialTime) ^ 2
  speedIsVelocityMagnitude : ∀ units time,
    speedReadout units (setup.speed time) =
      |velocityReadout units (setup.velocity time)|

/-! ## Derived event, displayed choices, and target -/

/-- Elapsed SI time from the stated initial event to the queried event. -/
def queryElapsedTimeSeconds (setup : MotorcycleMotionSetup) : ℝ :=
  timeInSeconds setup.queryTime - timeInSeconds setup.initialTime

/-- Requested signed position relative to the city-limits signpost, in metres. -/
def queriedPositionEastOfSignpostMeters
    (setup : MotorcycleMotionSetup) : ℝ :=
  positionInMeters (setup.position setup.queryTime) -
    positionInMeters setup.cityLimitsSignPosition

/-- The `25 m/s` event occurs `2.5 s` after the stated initial event. -/
lemma queryElapsedTime_from_speed
    (setup : MotorcycleMotionSetup)
    (_statement : MatchesProblemStatement setup)
    (_physical : HasPhysicalEastwardQueryEvent setup)
    (_kinematics : SatisfiesConstantAccelerationKinematics setup) :
    queryElapsedTimeSeconds setup = 5 / 2 := by
  have hpos :
      0 < velocityReadout UnitChoices.SI
        (setup.velocity setup.queryTime) := by
    exact _physical.queryVelocityPointsEast
  have hspeed :
      speedReadout UnitChoices.SI (setup.speed setup.queryTime) = 25 := by
    exact _statement.queriedSpeedMetersPerSecond
  have hmag :=
    _kinematics.speedIsVelocityMagnitude UnitChoices.SI setup.queryTime
  rw [abs_of_pos hpos] at hmag
  have hvq :
      velocityReadout UnitChoices.SI
        (setup.velocity setup.queryTime) = 25 := by
    linarith
  have hv0 :
      velocityReadout UnitChoices.SI
        (setup.velocity setup.initialTime) = 15 := by
    exact _statement.initialVelocityMetersPerSecond
  have ha :
      accelerationReadout UnitChoices.SI setup.constantAcceleration = 4 := by
    exact _statement.accelerationMetersPerSecondSquared
  change
    timeReadout UnitChoices.SI setup.queryTime -
        timeReadout UnitChoices.SI setup.initialTime =
      5 / 2
  nlinarith [
    _kinematics.velocityEvolution UnitChoices.SI setup.queryTime]

/-- Constant-acceleration kinematics gives the requested `55 m` position. -/
lemma queriedPosition_from_kinematics
    (setup : MotorcycleMotionSetup)
    (_statement : MatchesProblemStatement setup)
    (_physical : HasPhysicalEastwardQueryEvent setup)
    (_kinematics : SatisfiesConstantAccelerationKinematics setup) :
    queriedPositionEastOfSignpostMeters setup = 55 := by
  have hdt :=
    queryElapsedTime_from_speed setup _statement _physical _kinematics
  have hcity :
      positionReadout UnitChoices.SI setup.cityLimitsSignPosition = 0 := by
    exact _statement.cityLimitsSignIsOrigin
  have hx0 :
      positionReadout UnitChoices.SI
        (setup.position setup.initialTime) = 5 := by
    exact _statement.initialPositionMeters
  have hv0 :
      velocityReadout UnitChoices.SI
        (setup.velocity setup.initialTime) = 15 := by
    exact _statement.initialVelocityMetersPerSecond
  have ha :
      accelerationReadout UnitChoices.SI setup.constantAcceleration = 4 := by
    exact _statement.accelerationMetersPerSecondSquared
  have helapsed :
      timeReadout UnitChoices.SI setup.queryTime -
          timeReadout UnitChoices.SI setup.initialTime =
        5 / 2 := by
    exact hdt
  change
    positionReadout UnitChoices.SI (setup.position setup.queryTime) -
        positionReadout UnitChoices.SI setup.cityLimitsSignPosition =
      55
  nlinarith [
    _kinematics.positionEvolution UnitChoices.SI setup.queryTime]

/-- Labels of the four positions printed in the answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Position in metres printed beside each answer label. -/
def displayedPositionMeters : AnswerChoice → ℝ
  | .A => 27
  | .B => 55
  | .C => 45
  | .D => 65

/-- Answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A displayed position agrees with the position of the queried event. -/
def MatchesDisplayedPosition
    (setup : MotorcycleMotionSetup) (choice : AnswerChoice) : Prop :=
  queriedPositionEastOfSignpostMeters setup = displayedPositionMeters choice

/-- Exactly one displayed label agrees with the requested physical position. -/
def IsUniqueMatchingDisplayedChoice
    (setup : MotorcycleMotionSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPosition setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedPosition setup other → other = choice

/-!
At the future eastward event where the speed is `25 m/s`, the motorcyclist is
`55 m` east of the city-limits signpost.  Hence B is the unique displayed
answer matching the requested physical position.

This formalizes blueprint label `thm:physics:phyx_mini_0793:target`.
-/
theorem problem_phyx_mini_0793
    (setup : MotorcycleMotionSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedMotorcycleFigure setup)
    (_physical : HasPhysicalEastwardQueryEvent setup)
    (_kinematics : SatisfiesConstantAccelerationKinematics setup) :
    queriedPositionEastOfSignpostMeters setup = 55 ∧
      MatchesDisplayedPosition setup recordedAnswerChoice ∧
      IsUniqueMatchingDisplayedChoice setup recordedAnswerChoice := by
  have hposition :=
    queriedPosition_from_kinematics setup _statement _physical _kinematics
  refine ⟨hposition, ?_⟩
  unfold IsUniqueMatchingDisplayedChoice MatchesDisplayedPosition
  simp only [
    recordedAnswerChoice, displayedPositionMeters, hposition, true_and]
  intro other hother
  cases other with
  | A => norm_num [displayedPositionMeters] at hother
  | B => rfl
  | C => norm_num [displayedPositionMeters] at hother
  | D => norm_num [displayedPositionMeters] at hother

end PhyXMiniProblems.ProblemPhyXMini0793
