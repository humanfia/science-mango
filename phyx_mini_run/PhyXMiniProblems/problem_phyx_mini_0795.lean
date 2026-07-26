import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0795

open Dimension

/-!
# Position of a freely falling one-euro coin after three seconds

A one-euro coin is released from rest beside the Leaning Tower of Pisa.  The
primary figure chooses an upward-positive vertical axis `Y`, places the origin
at the release point, and labels samples at `0`, `1`, `2`, and `3` seconds.  It
also displays the constant vertical acceleration as
`a_y = -g = -9.8 m/s^2` and shows downward velocity arrows after release.

Position, time, velocity, acceleration, and gravitational-acceleration
magnitude are unit-independent Physlib quantities.  Real numbers below are
only coherent-unit readouts, schematic figure data, or displayed answer
values.

Assumption/target split:

* governing laws: the usual position and velocity equations for motion with
  constant vertical acceleration;
* previous-part results: none;
* figure/data readouts: `t_0 = 0`, `t_1 = 1 s`, `t_2 = 2 s`, `t_3 = 3 s`,
  `y_0 = 0`, `v_0 = 0`, an upward-positive `Y` axis, and
  `a_y = -g = -9.8 m/s^2`;
* current target conclusions: the exact metre readout `y_3 = -44.1` and the
  selection of the displayed `-44 m` answer, choice B.
-/

/-! ## Dimensionful vertical-kinematics quantities -/

/-- The physical dimension of signed vertical velocity, `L T^-1`. -/
def verticalVelocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of signed vertical acceleration, `L T^-2`. -/
def verticalAccelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical time coordinate. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed vertical position relative to the origin selected in the figure. -/
abbrev VerticalPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed component of vertical velocity. -/
abbrev VerticalVelocityQuantity : Type :=
  Dimensionful (WithDim verticalVelocityDimension ℝ)

/-- A signed component of vertical acceleration. -/
abbrev VerticalAccelerationQuantity : Type :=
  Dimensionful (WithDim verticalAccelerationDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim verticalAccelerationDimension NNReal)

/-- Read a physical time in an arbitrary coherent unit system. -/
def timeReadout (units : UnitChoices) (time : TimeQuantity) : ℝ :=
  ((time units).val : ℝ)

/-- Read a signed vertical position in an arbitrary coherent unit system. -/
def positionReadout
    (units : UnitChoices) (position : VerticalPositionQuantity) : ℝ :=
  (position units).val

/-- Read a signed vertical velocity in an arbitrary coherent unit system. -/
def velocityReadout
    (units : UnitChoices) (velocity : VerticalVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Read a signed vertical acceleration in an arbitrary coherent unit system. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : VerticalAccelerationQuantity) : ℝ :=
  (acceleration units).val

/-- Read a nonnegative acceleration magnitude in coherent units. -/
def accelerationMagnitudeReadout
    (units : UnitChoices) (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The four time labels printed beside the vertical trajectory. -/
inductive FigureSample where
  | t0
  | t1
  | t2
  | t3
  deriving DecidableEq, Fintype, Repr

/-- Qualitative vertical directions used by the axis and arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The physical object named in the problem statement. -/
inductive FallingObjectKind where
  | oneEuroCoin
  deriving DecidableEq, Repr

/-- The idealized physical model requested by the problem. -/
inductive VerticalMotionModel where
  | uniformGravityNegligibleAirResistance
  deriving DecidableEq, Repr

/-!
Literal information retained from the primary raster.  Its numerical fields
are displayed SI readouts; they are not definitions of the trajectory.
-/
structure FreeFallFigure where
  showsLeaningTower : Bool
  showsVerticalAxisY : Bool
  positiveYAxisDirection : VerticalDirection
  showsSamplePoint : FigureSample → Bool
  timeLabelSeconds : FigureSample → ℝ
  showsPositionQuestionMark : FigureSample → Bool
  showsVelocityQuestionMark : FigureSample → Bool
  velocityArrowDirection : FigureSample → Option VerticalDirection
  showsAccelerationArrow : Bool
  accelerationArrowDirection : VerticalDirection
  showsAccelerationRelationAyEqualsNegativeG : Bool
  accelerationLabelMetersPerSecondSquared : ℝ
  gravityMagnitudeLabelMetersPerSecondSquared : ℝ

/-!
Independent physical quantities of the fall.  In particular,
`verticalPosition` is an unconstrained trajectory field here: its value at
three seconds is not defined from any answer choice.
-/
structure CoinFreeFallSetup where
  objectKind : FallingObjectKind
  motionModel : VerticalMotionModel
  sampleTime : FigureSample → TimeQuantity
  verticalPosition : TimeQuantity → VerticalPositionQuantity
  verticalVelocity : TimeQuantity → VerticalVelocityQuantity
  verticalAcceleration : VerticalAccelerationQuantity
  gravityMagnitude : AccelerationMagnitudeQuantity
  figure : FreeFallFigure

/-- SI-second readout of one of the four labeled sampling times. -/
def sampleTimeInSeconds
    (setup : CoinFreeFallSetup) (sample : FigureSample) : ℝ :=
  timeReadout UnitChoices.SI (setup.sampleTime sample)

/-- SI-metre readout of position at one of the labeled sampling times. -/
def samplePositionInMeters
    (setup : CoinFreeFallSetup) (sample : FigureSample) : ℝ :=
  positionReadout UnitChoices.SI
    (setup.verticalPosition (setup.sampleTime sample))

/-- SI-metres-per-second readout at one of the labeled sampling times. -/
def sampleVelocityInMetersPerSecond
    (setup : CoinFreeFallSetup) (sample : FigureSample) : ℝ :=
  velocityReadout UnitChoices.SI
    (setup.verticalVelocity (setup.sampleTime sample))

/-- SI-metres-per-second-squared readout of the vertical acceleration. -/
def verticalAccelerationInMetersPerSecondSquared
    (setup : CoinFreeFallSetup) : ℝ :=
  accelerationReadout UnitChoices.SI setup.verticalAcceleration

/-- SI-metres-per-second-squared readout of the magnitude `g`. -/
def gravityMagnitudeInMetersPerSecondSquared
    (setup : CoinFreeFallSetup) : ℝ :=
  accelerationMagnitudeReadout UnitChoices.SI setup.gravityMagnitude

/-! ## Scenario, primary-image readouts, and governing laws -/

/-- The prose assumptions: a one-euro coin is released from rest in ideal free fall. -/
structure MatchesProblemDescription (setup : CoinFreeFallSetup) : Prop where
  objectIsOneEuroCoin : setup.objectKind = .oneEuroCoin
  idealFreeFallModel :
    setup.motionModel = .uniformGravityNegligibleAirResistance
  releasedFromRest : sampleVelocityInMetersPerSecond setup .t0 = 0

/-!
Primary-image evidence.  The question marks are recorded as graphical facts;
they deliberately impose no numerical condition on the unknown later
positions or velocities.
-/
structure MatchesSuppliedFigure (setup : CoinFreeFallSetup) : Prop where
  towerShown : setup.figure.showsLeaningTower = true
  verticalAxisYShown : setup.figure.showsVerticalAxisY = true
  yAxisPointsUpward : setup.figure.positiveYAxisDirection = .upward
  everySamplePointShown :
    ∀ sample, setup.figure.showsSamplePoint sample = true
  figureTimeLabelsMatchPhysicalTimes :
    ∀ sample,
      setup.figure.timeLabelSeconds sample = sampleTimeInSeconds setup sample
  timeLabelT0 : setup.figure.timeLabelSeconds .t0 = 0
  timeLabelT1 : setup.figure.timeLabelSeconds .t1 = 1
  timeLabelT2 : setup.figure.timeLabelSeconds .t2 = 2
  timeLabelT3 : setup.figure.timeLabelSeconds .t3 = 3
  initialPositionAtOrigin : samplePositionInMeters setup .t0 = 0
  initialVelocityLabel : sampleVelocityInMetersPerSecond setup .t0 = 0
  initialPositionIsGiven :
    setup.figure.showsPositionQuestionMark .t0 = false
  initialVelocityIsGiven :
    setup.figure.showsVelocityQuestionMark .t0 = false
  laterPositionsAreQuestionMarks :
    setup.figure.showsPositionQuestionMark .t1 = true ∧
      setup.figure.showsPositionQuestionMark .t2 = true ∧
      setup.figure.showsPositionQuestionMark .t3 = true
  laterVelocitiesAreQuestionMarks :
    setup.figure.showsVelocityQuestionMark .t1 = true ∧
      setup.figure.showsVelocityQuestionMark .t2 = true ∧
      setup.figure.showsVelocityQuestionMark .t3 = true
  noInitialVelocityArrow : setup.figure.velocityArrowDirection .t0 = none
  laterVelocityArrowsPointDown :
    setup.figure.velocityArrowDirection .t1 = some .downward ∧
      setup.figure.velocityArrowDirection .t2 = some .downward ∧
      setup.figure.velocityArrowDirection .t3 = some .downward
  accelerationArrowShown : setup.figure.showsAccelerationArrow = true
  accelerationArrowPointsDown :
    setup.figure.accelerationArrowDirection = .downward
  accelerationRelationShown :
    setup.figure.showsAccelerationRelationAyEqualsNegativeG = true
  accelerationLabelValue :
    setup.figure.accelerationLabelMetersPerSecondSquared = -(49 / 5 : ℝ)
  gravityMagnitudeLabelValue :
    setup.figure.gravityMagnitudeLabelMetersPerSecondSquared = 49 / 5
  accelerationLabelMatchesPhysicalQuantity :
    verticalAccelerationInMetersPerSecondSquared setup =
      setup.figure.accelerationLabelMetersPerSecondSquared
  gravityLabelMatchesPhysicalQuantity :
    gravityMagnitudeInMetersPerSecondSquared setup =
      setup.figure.gravityMagnitudeLabelMetersPerSecondSquared
  verticalAccelerationIsNegativeGravity :
    verticalAccelerationInMetersPerSecondSquared setup =
      -gravityMagnitudeInMetersPerSecondSquared setup

/-!
The standard constant-acceleration kinematics laws, stated in every coherent
unit choice.  They are general relations for arbitrary times and contain no
three-second position or answer-choice value.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : CoinFreeFallSetup) : Prop where
  positionLaw :
    ∀ units time,
      positionReadout units (setup.verticalPosition time) =
        positionReadout units
            (setup.verticalPosition (setup.sampleTime .t0)) +
          velocityReadout units
              (setup.verticalVelocity (setup.sampleTime .t0)) *
            (timeReadout units time -
              timeReadout units (setup.sampleTime .t0)) +
          (1 / 2 : ℝ) *
            accelerationReadout units setup.verticalAcceleration *
            (timeReadout units time -
              timeReadout units (setup.sampleTime .t0)) ^ 2
  velocityLaw :
    ∀ units time,
      velocityReadout units (setup.verticalVelocity time) =
        velocityReadout units
            (setup.verticalVelocity (setup.sampleTime .t0)) +
          accelerationReadout units setup.verticalAcceleration *
            (timeReadout units time -
              timeReadout units (setup.sampleTime .t0))

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Position readout in metres printed beside an answer choice. -/
def AnswerChoice.displayedPositionInMeters : AnswerChoice → ℝ
  | .A => -35
  | .B => -44
  | .C => -65
  | .D => -51

/-!
An answer is closest when its displayed metre value has no greater absolute
error than any other displayed value.  This distinguishes rounding from exact
equality of physical positions.
-/
def IsClosestAnswerChoice
    (positionInMeters : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |positionInMeters - selected.displayedPositionInMeters| ≤
      |positionInMeters - other.displayedPositionInMeters|

/-!
After three seconds the exact idealized position is `-44.1 m`; consequently
the displayed `-44 m` value, choice B, is closest.

This formalizes blueprint label `thm:physics:phyx_mini_0795:target`.
-/
theorem coinPositionAfterThreeSeconds_is_answerB
    (setup : CoinFreeFallSetup)
    (hProblem : MatchesProblemDescription setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    samplePositionInMeters setup .t3 = -(441 / 10 : ℝ) ∧
      IsClosestAnswerChoice (samplePositionInMeters setup .t3) .B := by
  have hTimeT0 : sampleTimeInSeconds setup .t0 = 0 := by
    calc
      sampleTimeInSeconds setup .t0 =
          setup.figure.timeLabelSeconds .t0 :=
        (hFigure.figureTimeLabelsMatchPhysicalTimes .t0).symm
      _ = 0 := hFigure.timeLabelT0
  have hTimeT3 : sampleTimeInSeconds setup .t3 = 3 := by
    calc
      sampleTimeInSeconds setup .t3 =
          setup.figure.timeLabelSeconds .t3 :=
        (hFigure.figureTimeLabelsMatchPhysicalTimes .t3).symm
      _ = 3 := hFigure.timeLabelT3
  have hAcceleration :
      verticalAccelerationInMetersPerSecondSquared setup =
        -(49 / 5 : ℝ) := by
    calc
      verticalAccelerationInMetersPerSecondSquared setup =
          setup.figure.accelerationLabelMetersPerSecondSquared :=
        hFigure.accelerationLabelMatchesPhysicalQuantity
      _ = -(49 / 5 : ℝ) := hFigure.accelerationLabelValue
  have hPositionLaw :
      samplePositionInMeters setup .t3 =
        samplePositionInMeters setup .t0 +
          sampleVelocityInMetersPerSecond setup .t0 *
            (sampleTimeInSeconds setup .t3 -
              sampleTimeInSeconds setup .t0) +
          (1 / 2 : ℝ) *
            verticalAccelerationInMetersPerSecondSquared setup *
            (sampleTimeInSeconds setup .t3 -
              sampleTimeInSeconds setup .t0) ^ 2 := by
    simpa [samplePositionInMeters, sampleVelocityInMetersPerSecond,
      sampleTimeInSeconds, verticalAccelerationInMetersPerSecondSquared] using
      hKinematics.positionLaw UnitChoices.SI (setup.sampleTime .t3)
  have hPosition :
      samplePositionInMeters setup .t3 = -(441 / 10 : ℝ) := by
    rw [hFigure.initialPositionAtOrigin, hProblem.releasedFromRest,
      hTimeT3, hTimeT0, hAcceleration] at hPositionLaw
    norm_num at hPositionLaw ⊢
    exact hPositionLaw
  refine ⟨hPosition, ?_⟩
  rw [hPosition]
  intro other
  cases other <;>
    norm_num [AnswerChoice.displayedPositionInMeters]

end PhyXMiniProblems.ProblemPhyXMini0795
