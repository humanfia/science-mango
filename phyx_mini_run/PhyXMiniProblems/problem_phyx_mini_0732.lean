import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Coordinating green lights for a traffic platoon

The supplied figure shows a one-way street directed from left to right through
intersections `1`, `2`, and `3`.  The marked separations are `D₁₂` and `D₂₃`.
A platoon travels at the speed limit `vₚ`.  At both intersections `2` and `3`,
the green begins when the platoon leader is the same physical distance `d`
upstream of the intersection.

Lengths, time coordinates, and speed are unit-independent Physlib quantities.
Real numbers occur only after a coherent choice of length and time units has
been made.  In particular, the delay between the two green onsets is an
observable derived from the event times; it is not defined to equal an answer
choice.

Assumption/target boundary:

* `MatchesPrimaryTrafficFigure` records the labels and qualitative geometry
  visible in the bitmap.
* `SatisfiesStreetDistanceGeometry` relates the physical intersection
  positions to the two marked segment lengths.
* `MatchesGreenTriggerProtocol` records the common upstream trigger distance
  `d` at intersections `2` and `3`.
* `SatisfiesUniformPlatoonMotion` is the governing law
  `displacement = speed * elapsed time`.
* The formula `green₃ - green₂ = D₂₃ / vₚ` occurs only in the final theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0732

open Dimension

/-! ## Dimensionful quantities and coherent scalar readouts -/

/-- A unit-independent physical length or signed coordinate along the street. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical time coordinate. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- The nonnegative, unit-independent physical speed type supplied by Physlib. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a length or longitudinal coordinate in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({UnitChoices.SI with length := unit} : UnitChoices)).val

/-- Read a time coordinate in the selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time ({UnitChoices.SI with time := unit} : UnitChoices)).val

/-- Read a speed in the coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed ({UnitChoices.SI with
      length := lengthUnit, time := timeUnit} : UnitChoices)).val : ℝ)

/-! ## Street, figure, and answer-choice labels -/

/-- The three numbered intersections in their left-to-right order. -/
inductive Intersection where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The two consecutive street segments carrying the labels `D₁₂` and `D₂₃`. -/
inductive StreetSegment where
  | between12
  | between23
  deriving DecidableEq, Fintype, Repr

/-- The left endpoint of a directed street segment. -/
def StreetSegment.startIntersection : StreetSegment → Intersection
  | .between12 => .one
  | .between23 => .two

/-- The right endpoint of a directed street segment. -/
def StreetSegment.finishIntersection : StreetSegment → Intersection
  | .between12 => .two
  | .between23 => .three

/-- Literal distance labels printed below the street in the primary figure. -/
inductive SegmentDistanceLabel where
  | D12
  | D23
  deriving DecidableEq, Fintype, Repr

/-- The printed label belonging to each directed segment. -/
def StreetSegment.expectedDistanceLabel : StreetSegment → SegmentDistanceLabel
  | .between12 => .D12
  | .between23 => .D23

/-- Direction of travel along the horizontal street axis. -/
inductive HorizontalDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
A structured transcription of the primary bitmap.  It stores only discrete
labels and qualitative visible features; physical distances are kept in the
setup below.
-/
structure TrafficControlFigure where
  intersectionShown : Intersection → Bool
  oneWaySignShown : Bool
  oneWayArrowDirection : HorizontalDirection
  distanceMarkerShown : StreetSegment → Bool
  distanceMarkerStart : StreetSegment → Intersection
  distanceMarkerFinish : StreetSegment → Intersection
  distanceMarkerLabel : StreetSegment → SegmentDistanceLabel
  twoTravelLanesShown : Bool
  platoonCarsShownUpstreamOfIntersectionOne : Bool

/-! ## Physical setup and figure-derived geometry -/

/-!
Independent physical quantities and event observables.  The green-onset times
and leader trajectory are free fields here; their relations are imposed by
separate protocol and kinematics predicates.
-/
structure TrafficSignalSetup where
  intersectionPosition : Intersection → LengthQuantity
  segmentDistance : StreetSegment → LengthQuantity
  greenTriggerDistance : LengthQuantity
  speedLimit : SpeedQuantity
  greenOnsetTime : Intersection → TimeQuantity
  leaderPosition : TimeQuantity → LengthQuantity
  leaderReachesIntersectionTwoAt : TimeQuantity
  platoonTravelDirection : HorizontalDirection
  platoonTravelsAtSpeedLimit : Bool
  figure : TrafficControlFigure

/-- Qualitative labels and geometry read directly from `732.png`. -/
structure MatchesPrimaryTrafficFigure (setup : TrafficSignalSetup) : Prop where
  allThreeIntersectionsShown :
    ∀ intersection, setup.figure.intersectionShown intersection = true
  oneWaySignIsShown : setup.figure.oneWaySignShown = true
  oneWayArrowPointsRight :
    setup.figure.oneWayArrowDirection = .positiveX
  bothDistanceMarkersShown :
    ∀ segment, setup.figure.distanceMarkerShown segment = true
  distanceMarkersStartAtExpectedIntersections :
    ∀ segment,
      setup.figure.distanceMarkerStart segment = segment.startIntersection
  distanceMarkersFinishAtExpectedIntersections :
    ∀ segment,
      setup.figure.distanceMarkerFinish segment = segment.finishIntersection
  distanceMarkersCarryExpectedLabels :
    ∀ segment,
      setup.figure.distanceMarkerLabel segment = segment.expectedDistanceLabel
  twoTravelLanesAreShown : setup.figure.twoTravelLanesShown = true
  carsAreDrawnUpstreamOfIntersectionOne :
    setup.figure.platoonCarsShownUpstreamOfIntersectionOne = true

/-!
The prose says that the leaders have reached intersection `2`, continue in the
positive street direction, and travel at the speed limit.  The earlier green
onset at intersection `2` remains a separate event.
-/
structure MatchesPlatoonScenario (setup : TrafficSignalSetup) : Prop where
  platoonTravelsRight : setup.platoonTravelDirection = .positiveX
  platoonUsesSpeedLimit : setup.platoonTravelsAtSpeedLimit = true
  leaderAtIntersectionTwo :
    setup.leaderPosition setup.leaderReachesIntersectionTwoAt =
      setup.intersectionPosition .two
  greenAtTwoPrecedesArrivalAtTwo : ∀ unit : TimeUnit,
    timeReadout unit (setup.greenOnsetTime .two) <
      timeReadout unit setup.leaderReachesIntersectionTwoAt

/-!
The marked physical segment length is the difference of its endpoint
coordinates.  This records both `D₁₂` and `D₂₃`, even though only `D₂₃`
survives in the requested delay.
-/
structure SatisfiesStreetDistanceGeometry
    (setup : TrafficSignalSetup) : Prop where
  segmentSeparation : ∀ (segment : StreetSegment) (unit : LengthUnit),
    lengthReadout unit
          (setup.intersectionPosition segment.finishIntersection) -
        lengthReadout unit
          (setup.intersectionPosition segment.startIntersection) =
      lengthReadout unit (setup.segmentDistance segment)

/-!
At each relevant green onset, the leader is the same physical distance `d`
upstream of that intersection.  These are trigger-event readouts, not a delay
formula.
-/
structure MatchesGreenTriggerProtocol
    (setup : TrafficSignalSetup) : Prop where
  greenBeginsAtCommonUpstreamDistance :
    ∀ (intersection : Intersection) (_relevant : intersection = .two ∨ intersection = .three)
      (unit : LengthUnit),
      lengthReadout unit (setup.intersectionPosition intersection) -
          lengthReadout unit
            (setup.leaderPosition (setup.greenOnsetTime intersection)) =
        lengthReadout unit setup.greenTriggerDistance

/-!
Nondegeneracy and event ordering for the physical branch depicted in the
problem.  No magnitude for the requested delay occurs here.
-/
structure HasPhysicalTrafficParameters
    (setup : TrafficSignalSetup) : Prop where
  segmentDistancesPositive : ∀ segment unit,
    0 < lengthReadout unit (setup.segmentDistance segment)
  triggerDistancePositive : ∀ unit,
    0 < lengthReadout unit setup.greenTriggerDistance
  speedLimitPositive : ∀ lengthUnit timeUnit,
    0 < speedReadout lengthUnit timeUnit setup.speedLimit
  greenAtThreeBeginsLater : ∀ unit,
    timeReadout unit (setup.greenOnsetTime .two) <
      timeReadout unit (setup.greenOnsetTime .three)

/-!
Governing uniform-motion law during the interval from the onset of green at
intersection `2` through the onset at intersection `3`.  It is deliberately
quantified over arbitrary event times in that interval, rather than assuming
the requested endpoint-delay formula.
-/
structure SatisfiesUniformPlatoonMotion
    (setup : TrafficSignalSetup) : Prop where
  displacementEqualsSpeedTimesElapsed :
    ∀ (startTime finishTime : TimeQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      timeReadout timeUnit (setup.greenOnsetTime .two) ≤
          timeReadout timeUnit startTime →
      timeReadout timeUnit startTime ≤ timeReadout timeUnit finishTime →
      timeReadout timeUnit finishTime ≤
          timeReadout timeUnit (setup.greenOnsetTime .three) →
      lengthReadout lengthUnit (setup.leaderPosition finishTime) -
          lengthReadout lengthUnit (setup.leaderPosition startTime) =
        speedReadout lengthUnit timeUnit setup.speedLimit *
          (timeReadout timeUnit finishTime -
            timeReadout timeUnit startTime)

/-! ## Displayed formulas and requested delay -/

/-- Scalar readout of the onset delay of green `3` relative to green `2`. -/
def greenOnsetDelayReadout
    (setup : TrafficSignalSetup) (unit : TimeUnit) : ℝ :=
  timeReadout unit (setup.greenOnsetTime .three) -
    timeReadout unit (setup.greenOnsetTime .two)

/-!
The delay expression printed beside an answer label.  Choice `A` uses
`D₁₃ = D₁₂ + D₂₃`, while choices `B`, `C`, and `D` use the stated multiples
of `D₂₃`.
-/
def displayedDelayReadout
    (setup : TrafficSignalSetup)
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : AnswerChoice → ℝ
  | .A =>
      (lengthReadout lengthUnit (setup.segmentDistance .between12) +
        lengthReadout lengthUnit (setup.segmentDistance .between23)) /
          speedReadout lengthUnit timeUnit setup.speedLimit
  | .B =>
      (2 * lengthReadout lengthUnit (setup.segmentDistance .between23)) /
        speedReadout lengthUnit timeUnit setup.speedLimit
  | .C =>
      lengthReadout lengthUnit (setup.segmentDistance .between23) /
        speedReadout lengthUnit timeUnit setup.speedLimit
  | .D =>
      lengthReadout lengthUnit (setup.segmentDistance .between23) /
        (2 * speedReadout lengthUnit timeUnit setup.speedLimit)

/-!
The common trigger offset `d` cancels between the two green-onset events.
Uniform motion therefore makes the required delay exactly `D₂₃ / vₚ`, which
is displayed answer C.

Blueprint label: `thm:physics:phyx_mini_0732:target`.
-/
theorem problem_phyx_mini_0732
    (setup : TrafficSignalSetup)
    (_scenario : MatchesPlatoonScenario setup)
    (_figure : MatchesPrimaryTrafficFigure setup)
    (_geometry : SatisfiesStreetDistanceGeometry setup)
    (_trigger : MatchesGreenTriggerProtocol setup)
    (_physical : HasPhysicalTrafficParameters setup)
    (_motion : SatisfiesUniformPlatoonMotion setup) :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      greenOnsetDelayReadout setup timeUnit =
        lengthReadout lengthUnit (setup.segmentDistance .between23) /
          speedReadout lengthUnit timeUnit setup.speedLimit := by
  intro lengthUnit timeUnit
  have htime :
      timeReadout timeUnit (setup.greenOnsetTime .two) ≤
        timeReadout timeUnit (setup.greenOnsetTime .three) :=
    le_of_lt (_physical.greenAtThreeBeginsLater timeUnit)
  have hmotion :=
    _motion.displacementEqualsSpeedTimesElapsed
      (setup.greenOnsetTime .two) (setup.greenOnsetTime .three)
      lengthUnit timeUnit (le_refl _) htime (le_refl _)
  have htriggerTwo :=
    _trigger.greenBeginsAtCommonUpstreamDistance
      .two (Or.inl rfl) lengthUnit
  have htriggerThree :=
    _trigger.greenBeginsAtCommonUpstreamDistance
      .three (Or.inr rfl) lengthUnit
  have hgeometry :=
    _geometry.segmentSeparation .between23 lengthUnit
  simp only [StreetSegment.finishIntersection, StreetSegment.startIntersection] at hgeometry
  have hdisplacement :
      lengthReadout lengthUnit
          (setup.leaderPosition (setup.greenOnsetTime .three)) -
        lengthReadout lengthUnit
          (setup.leaderPosition (setup.greenOnsetTime .two)) =
        lengthReadout lengthUnit (setup.segmentDistance .between23) := by
    linarith
  have hspeed :
      speedReadout lengthUnit timeUnit setup.speedLimit ≠ 0 :=
    ne_of_gt (_physical.speedLimitPositive lengthUnit timeUnit)
  unfold greenOnsetDelayReadout
  apply (eq_div_iff hspeed).2
  rw [mul_comm, ← hmotion]
  exact hdisplacement

end PhyXMiniProblems.ProblemPhyXMini0732
