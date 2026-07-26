import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0829

open Dimension

/-!
# Velocity from a position-versus-time graph

The primary figure shows two students on roller blades.  Their signed
one-dimensional positions are plotted against time as straight traces.  The
figure marks, for student A, an elapsed time of `0.40 s` and a displacement of
`2.0 m`; for student B it marks `0.50 s` and `-1.0 m`.  The question asks for
student A's signed x-velocity component.

Positions, displacements, times, durations, and velocity components are kept
as unit-independent Physlib quantities.  Real numbers occur only as readouts
in the metres, seconds, and metres-per-second units printed in the figure.

Assumption/target split:

* `MatchesRollerBladeScenario` records that both labeled participants are
  students on roller blades.
* `MatchesSuppliedPositionTimeFigure` records the axes, units, labeled ticks,
  trace labels and trends, interval endpoints, and finite-difference values
  read from image `829.png`.  It records the qualitative annotation that
  velocity is obtained as graph slope, but does not assume either printed
  numerical velocity.
* `SatisfiesPositionTimeGraphVelocityLaw` is the governing kinematic law that
  a straight position-time trace has signed velocity equal to displacement
  divided by elapsed time.
* There are no previous-part results.
* Student A's value `5.0 m/s` and the unique match with answer B occur only in
  the final theorem's conclusion.
-/

/-! ## Dimensionful kinematic quantities and SI readouts -/

/-- A signed physical position on the graph's one-dimensional x-axis. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed physical displacement along the graph's x-axis. -/
abbrev SignedDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate measured from the graph's time origin. -/
abbrev TimeCoordinateQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative physical elapsed-time interval. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional velocity component, with dimension length/time. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed physical position in the coherent units selected by `units`. -/
def positionReadout
    (units : UnitChoices) (position : SignedPositionQuantity) : ℝ :=
  (position units).val

/-- Read a signed physical displacement in coherent selected units. -/
def displacementReadout
    (units : UnitChoices) (displacement : SignedDisplacementQuantity) : ℝ :=
  (displacement units).val

/-- Read a physical time coordinate in the coherent units selected by `units`. -/
def timeReadout
    (units : UnitChoices) (time : TimeCoordinateQuantity) : ℝ :=
  (time units).val

/-- Read a nonnegative duration in the coherent units selected by `units`. -/
def durationReadout
    (units : UnitChoices) (duration : DurationQuantity) : ℝ :=
  ((duration units).val : ℝ)

/-- Read a signed velocity component in the coherent units selected by `units`. -/
def velocityReadout
    (units : UnitChoices) (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity units).val

/-- SI-metre readout of a signed position. -/
def positionInMeters (position : SignedPositionQuantity) : ℝ :=
  positionReadout UnitChoices.SI position

/-- SI-metre readout of a signed displacement. -/
def displacementInMeters (displacement : SignedDisplacementQuantity) : ℝ :=
  displacementReadout UnitChoices.SI displacement

/-- SI-second readout of a time coordinate. -/
def timeInSeconds (time : TimeCoordinateQuantity) : ℝ :=
  timeReadout UnitChoices.SI time

/-- SI-second readout of a nonnegative duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout UnitChoices.SI duration

/-- SI-metre-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout UnitChoices.SI velocity

/-! ## Participants and primary-figure vocabulary -/

/-- The two labeled students whose traces appear in the graph. -/
inductive Student where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Physical role of each moving participant in the scenario. -/
inductive ParticipantKind where
  | studentOnRollerBlades
  deriving DecidableEq, Repr

/-- The horizontal and vertical axes of the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity represented on a graph axis. -/
inductive AxisQuantity where
  | time
  | xPosition
  deriving DecidableEq, Repr

/-- Unit printed beside a graph axis. -/
inductive AxisUnit where
  | seconds
  | meters
  deriving DecidableEq, Repr

/-- Geometric shape of a student's trace in the supplied graph. -/
inductive TraceGeometry where
  | straightLine
  deriving DecidableEq, Repr

/-- Qualitative direction of a trace as time increases. -/
inductive TraceTrend where
  | increasing
  | decreasing
  deriving DecidableEq, Repr

/-- The non-numerical slope formula visibly annotated beside each trace. -/
inductive SlopeAnnotation where
  | velocityEqualsDeltaPositionOverDeltaTime
  deriving DecidableEq, Repr

/-!
Typed transcription of image `829.png`.  Endpoint quantities are physical,
not bare scalar coordinates.  The two numerical slope results printed in blue
are intentionally not fields: student A's is the current target, and both are
derivable from the finite-difference data and the governing law.
-/
structure PositionTimeGraphFigure where
  axisQuantity : GraphAxis → AxisQuantity
  axisUnit : GraphAxis → AxisUnit
  axisLabel : GraphAxis → String
  labeledTimeTicksSeconds : List ℝ
  labeledPositionTicksMeters : List ℝ
  traceLabel : Student → String
  traceGeometry : Student → TraceGeometry
  traceTrend : Student → TraceTrend
  intervalStartTime : Student → TimeCoordinateQuantity
  intervalEndTime : Student → TimeCoordinateQuantity
  intervalStartPosition : Student → SignedPositionQuantity
  intervalEndPosition : Student → SignedPositionQuantity
  displayedElapsedTime : Student → DurationQuantity
  displayedDisplacement : Student → SignedDisplacementQuantity
  slopeAnnotation : Student → SlopeAnnotation

/-!
The physical motions and the figure that displays them.  Velocity components
are observables constrained by the governing law below; no numerical velocity
answer is stored in this setup.
-/
structure RollerBladeMotionSetup where
  participantKind : Student → ParticipantKind
  positionAt : Student → TimeCoordinateQuantity → SignedPositionQuantity
  velocityX : Student → SignedVelocityQuantity
  figure : PositionTimeGraphFigure

/-! ## Scenario and primary-figure evidence -/

/-- Both participants named in the problem are students on roller blades. -/
structure MatchesRollerBladeScenario
    (setup : RollerBladeMotionSetup) : Prop where
  everyParticipantIsAStudentOnRollerBlades :
    ∀ student, setup.participantKind student = .studentOnRollerBlades

/-!
Literal axis, tick, label, trend, and finite-difference data from the primary
bitmap.  The start and end points are tied to the physical trajectories.  No
field states student A's velocity or selects an answer choice.
-/
structure MatchesSuppliedPositionTimeFigure
    (setup : RollerBladeMotionSetup) : Prop where
  horizontalAxisShowsTime :
    setup.figure.axisQuantity .horizontal = .time
  verticalAxisShowsPosition :
    setup.figure.axisQuantity .vertical = .xPosition
  horizontalAxisUsesSeconds :
    setup.figure.axisUnit .horizontal = .seconds
  verticalAxisUsesMeters :
    setup.figure.axisUnit .vertical = .meters
  horizontalAxisLabel : setup.figure.axisLabel .horizontal = "t (s)"
  verticalAxisLabel : setup.figure.axisLabel .vertical = "x (m)"
  labeledTimeTicks :
    setup.figure.labeledTimeTicksSeconds =
      [(1 : ℝ) / 5, (2 : ℝ) / 5, (3 : ℝ) / 5, (4 : ℝ) / 5, 1]
  labeledPositionTicks :
    setup.figure.labeledPositionTicksMeters = [-2, 0, 2, 4, 6, 8]
  traceALabel : setup.figure.traceLabel .A = "Student A"
  traceBLabel : setup.figure.traceLabel .B = "Student B"
  bothTracesAreStraight :
    ∀ student, setup.figure.traceGeometry student = .straightLine
  traceAIncreases : setup.figure.traceTrend .A = .increasing
  traceBDecreases : setup.figure.traceTrend .B = .decreasing
  intervalStartsOnTrajectory : ∀ student,
    setup.figure.intervalStartPosition student =
      setup.positionAt student (setup.figure.intervalStartTime student)
  intervalEndsOnTrajectory : ∀ student,
    setup.figure.intervalEndPosition student =
      setup.positionAt student (setup.figure.intervalEndTime student)
  displayedElapsedTimeMatchesEndpoints : ∀ student,
    durationInSeconds (setup.figure.displayedElapsedTime student) =
      timeInSeconds (setup.figure.intervalEndTime student) -
        timeInSeconds (setup.figure.intervalStartTime student)
  displayedDisplacementMatchesEndpoints : ∀ student,
    displacementInMeters (setup.figure.displayedDisplacement student) =
      positionInMeters (setup.figure.intervalEndPosition student) -
        positionInMeters (setup.figure.intervalStartPosition student)
  intervalAStartTime :
    timeInSeconds (setup.figure.intervalStartTime .A) = 0
  intervalAEndTime :
    timeInSeconds (setup.figure.intervalEndTime .A) = (2 : ℝ) / 5
  intervalAStartPosition :
    positionInMeters (setup.figure.intervalStartPosition .A) = 2
  intervalAEndPosition :
    positionInMeters (setup.figure.intervalEndPosition .A) = 4
  displayedElapsedTimeA :
    durationInSeconds (setup.figure.displayedElapsedTime .A) = (2 : ℝ) / 5
  displayedDisplacementA :
    displacementInMeters (setup.figure.displayedDisplacement .A) = 2
  intervalBStartTime :
    timeInSeconds (setup.figure.intervalStartTime .B) = 0
  intervalBEndTime :
    timeInSeconds (setup.figure.intervalEndTime .B) = (1 : ℝ) / 2
  intervalBStartPosition :
    positionInMeters (setup.figure.intervalStartPosition .B) = 1
  intervalBEndPosition :
    positionInMeters (setup.figure.intervalEndPosition .B) = 0
  displayedElapsedTimeB :
    durationInSeconds (setup.figure.displayedElapsedTime .B) = (1 : ℝ) / 2
  displayedDisplacementB :
    displacementInMeters (setup.figure.displayedDisplacement .B) = -1
  bothSlopeAnnotationsShowTheKinematicFormula : ∀ student,
    setup.figure.slopeAnnotation student =
      .velocityEqualsDeltaPositionOverDeltaTime

/-! ## Governing kinematic law -/

/-!
On a straight position-versus-time trace, the signed velocity component is
the displacement over the nonzero elapsed time.  This law is stated uniformly
for A and B and contains no numerical velocity or answer-choice conclusion.
-/
structure SatisfiesPositionTimeGraphVelocityLaw
    (setup : RollerBladeMotionSetup) : Prop where
  displayedIntervalsAreNonzero : ∀ student,
    durationInSeconds (setup.figure.displayedElapsedTime student) ≠ 0
  velocityIsGraphSlope : ∀ student,
    velocityInMetersPerSecond (setup.velocityX student) =
      displacementInMeters (setup.figure.displayedDisplacement student) /
        durationInSeconds (setup.figure.displayedElapsedTime student)

/-! ## Derived readouts, answer choices, and current target -/

/-- The two finite-difference readouts marked for student A in the figure. -/
lemma studentA_finiteDifference_readouts
    (setup : RollerBladeMotionSetup)
    (_figure : MatchesSuppliedPositionTimeFigure setup) :
    durationInSeconds (setup.figure.displayedElapsedTime .A) = (2 : ℝ) / 5 ∧
      displacementInMeters (setup.figure.displayedDisplacement .A) = 2 := by
  exact
    ⟨_figure.displayedElapsedTimeA,
      _figure.displayedDisplacementA⟩

/-- Labels of the four velocities listed as possible answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer label. -/
def AnswerChoice.displayedMetersPerSecond : AnswerChoice → ℝ
  | .A => 22 / 5
  | .B => 5
  | .C => 2
  | .D => 3

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A displayed choice agrees with student A's physical velocity component. -/
def MatchesStudentAVelocityChoice
    (setup : RollerBladeMotionSetup) (choice : AnswerChoice) : Prop :=
  velocityInMetersPerSecond (setup.velocityX .A) =
    choice.displayedMetersPerSecond

/-- Exactly one displayed answer agrees with student A's velocity component. -/
def IsUniqueMatchingStudentAVelocityChoice
    (setup : RollerBladeMotionSetup) (choice : AnswerChoice) : Prop :=
  MatchesStudentAVelocityChoice setup choice ∧
    ∀ other, MatchesStudentAVelocityChoice setup other → other = choice

/-!
Student A's straight trace rises `2.0 m` in `0.40 s`, so its signed
x-velocity is `+5.0 m/s`.  This is the unique displayed value at the recorded
answer label B.

This formalizes `thm:physics:phyx_mini_0829:target`.
-/
theorem studentA_velocity_is_five_meters_per_second
    (setup : RollerBladeMotionSetup)
    (_scenario : MatchesRollerBladeScenario setup)
    (_figure : MatchesSuppliedPositionTimeFigure setup)
    (_velocityLaw : SatisfiesPositionTimeGraphVelocityLaw setup) :
    velocityInMetersPerSecond (setup.velocityX .A) = 5 ∧
      IsUniqueMatchingStudentAVelocityChoice setup recordedAnswerChoice := by
  have hReadouts := studentA_finiteDifference_readouts setup _figure
  have hVelocity := _velocityLaw.velocityIsGraphSlope Student.A
  rw [hReadouts.2, hReadouts.1] at hVelocity
  norm_num at hVelocity
  refine ⟨hVelocity, ?_⟩
  constructor
  · simpa [MatchesStudentAVelocityChoice, recordedAnswerChoice,
      AnswerChoice.displayedMetersPerSecond] using hVelocity
  · intro other hOther
    cases other with
    | A =>
        change velocityInMetersPerSecond (setup.velocityX .A) = 22 / 5 at hOther
        exfalso
        norm_num at hOther
        linarith
    | B => rfl
    | C =>
        change velocityInMetersPerSecond (setup.velocityX .A) = 2 at hOther
        exfalso
        linarith
    | D =>
        change velocityInMetersPerSecond (setup.velocityX .A) = 3 at hOther
        exfalso
        linarith

end PhyXMiniProblems.ProblemPhyXMini0829
