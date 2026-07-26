import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Bob and Susan meet between Chicago and Pittsburgh

Bob leaves Chicago at 9:00 A.M. and moves east at a steady `60 mph`.  Susan
leaves Pittsburgh at the same instant, `400 miles` east of Chicago, and moves
west at a steady `40 mph`.  The supplied figure uses a horizontal `x`-axis,
labels their initial and meeting state tuples, marks both acceleration vectors
as zero, and labels their common position with “Meet here”.

Positions, clock times, signed velocity components, and signed acceleration
components are represented by unit-independent Physlib quantities.  Real
numbers occur only as named unit readouts and as the displayed answer-choice
values.

Assumption/target boundary:

* `MatchesTravelScenario` records the travelers, homes, directions, and
  constant-velocity motion regime;
* `MatchesProblemReadouts` records 9:00 A.M., the 400-mile separation, and the
  signed `+60 mph` and `-40 mph` velocity components;
* `MatchesSuppliedFigure` records the primary-image labels and geometry;
* `SatisfiesZeroAccelerationLaw` and `SatisfiesUniformMotionLaw` are the
  governing kinematic laws;
* `IsMeetingEvent` says only that the designated later event has equal
  positions; and
* the `240 mile` displacement and hence recorded choice B occur only in the
  conclusion of the final theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0830

open Dimension

/-! ## Dimensionful quantities and customary-unit readouts -/

/-- A signed one-dimensional position with the physical dimension of length. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A clock time, represented as a signed physical time quantity. -/
abbrev ClockTimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A signed `x`-velocity component with dimension length per time. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed `x`-acceleration component with dimension length per time squared. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a signed position in a selected physical length unit. -/
def positionReadout
    (lengthUnit : LengthUnit) (position : SignedPositionQuantity) : ℝ :=
  (position ({UnitChoices.SI with length := lengthUnit} : UnitChoices)).val

/-- Read a clock time in a selected physical time unit. -/
def clockTimeReadout
    (timeUnit : TimeUnit) (time : ClockTimeQuantity) : ℝ :=
  (time ({UnitChoices.SI with time := timeUnit} : UnitChoices)).val

/-- Read a signed velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity ({UnitChoices.SI with
    length := lengthUnit, time := timeUnit} : UnitChoices)).val

/-- Read a signed acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration ({UnitChoices.SI with
    length := lengthUnit, time := timeUnit} : UnitChoices)).val

/-- Mile readout used for the Chicago--Pittsburgh coordinate axis. -/
def positionInMiles (position : SignedPositionQuantity) : ℝ :=
  positionReadout LengthUnit.miles position

/-- Hour readout used for the two clock-event labels `t₀` and `t_f`. -/
def clockTimeInHours (time : ClockTimeQuantity) : ℝ :=
  clockTimeReadout TimeUnit.hours time

/-- Miles-per-hour readout of a signed horizontal velocity component. -/
def velocityInMilesPerHour (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.miles TimeUnit.hours velocity

/-- Miles-per-hour-squared readout of a signed horizontal acceleration. -/
def accelerationInMilesPerHourSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.miles TimeUnit.hours acceleration

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two travelers named in the problem and the supplied image. -/
inductive Traveler where
  | bob
  | susan
  deriving DecidableEq, Fintype, Repr

/-- The two endpoint cities on the horizontal route. -/
inductive City where
  | chicago
  | pittsburgh
  deriving DecidableEq, Fintype, Repr

/-- The positive and negative directions of the pictured `x`-axis. -/
inductive AxisDirection where
  | east
  | west
  deriving DecidableEq, Repr

/-- The initial and final state-tuples drawn below the cars. -/
inductive FigureEvent where
  | departure
  | meeting
  deriving DecidableEq, Fintype, Repr

/-- The idealized translational motion regime stated in the prose. -/
inductive MotionRegime where
  | constantVelocity
  | other
  deriving DecidableEq, Repr

/-- Literal semantic labels appearing in the primary image. -/
inductive FigureLabel where
  | xAxis
  | chicago
  | pittsburgh
  | bob
  | susan
  | meetHere
  | velocityBob
  | velocitySusan
  | zeroAccelerationBob
  | zeroAccelerationSusan
  deriving DecidableEq, Fintype, Repr

/-!
A typed transcription of `phyx_data/test_image/830.png`.  The tuple flags refer
to `(x₀B, (vₓ)B, t₀)`, `(x₀S, (vₓ)S, t₀)` and the corresponding two
meeting tuples with `x_f` and `t_f`.  No numeric meeting coordinate is stored
in this figure object.
-/
structure ChicagoPittsburghMeetingFigure where
  showsLabel : FigureLabel → Bool
  carShown : Traveler → FigureEvent → Bool
  stateTupleShown : Traveler → FigureEvent → Bool
  cityAtAxisEndpoint : City → Bool
  cityOrderLeftToRight : City → City → Bool
  velocityArrowShown : Traveler → Bool
  velocityArrowDirection : Traveler → AxisDirection
  zeroAccelerationVectorShown : Traveler → Bool
  motionSampleMarkersShown : Traveler → Bool
  commonMeetingMarkerShown : Bool

/-!
Independent physical quantities and time-indexed observables.  `departureTime`
is shared by construction, reflecting that Bob and Susan leave simultaneously.
The meeting coordinate is not a field and is not fixed by any definition.
-/
structure TwoTravelerMeetingSetup where
  figure : ChicagoPittsburghMeetingFigure
  homeCity : Traveler → City
  cityPosition : City → SignedPositionQuantity
  departureTime : ClockTimeQuantity
  meetingTime : ClockTimeQuantity
  xPositionAt : Traveler → ClockTimeQuantity → SignedPositionQuantity
  constantXVelocity : Traveler → SignedVelocityQuantity
  xAccelerationAt : Traveler → ClockTimeQuantity → SignedAccelerationQuantity
  travelDirection : Traveler → AxisDirection
  motionRegime : Traveler → MotionRegime
  positiveAxisDirection : AxisDirection

/-! ## Scenario, figure evidence, and calibrated data -/

/-- Qualitative prose content, with no numerical meeting time or position. -/
structure MatchesTravelScenario (setup : TwoTravelerMeetingSetup) : Prop where
  positiveXPointsEast : setup.positiveAxisDirection = .east
  bobLivesInChicago : setup.homeCity .bob = .chicago
  susanLivesInPittsburgh : setup.homeCity .susan = .pittsburgh
  bobStartsAtHome :
    setup.xPositionAt .bob setup.departureTime =
      setup.cityPosition (setup.homeCity .bob)
  susanStartsAtHome :
    setup.xPositionAt .susan setup.departureTime =
      setup.cityPosition (setup.homeCity .susan)
  bothUseConstantVelocityMotion :
    ∀ traveler, setup.motionRegime traveler = .constantVelocity
  bobTravelsEast : setup.travelDirection .bob = .east
  susanTravelsWest : setup.travelDirection .susan = .west

/-!
The numerical values stated in the problem.  Pittsburgh's location is given
as a displacement from Chicago, so the choice of Chicago as coordinate origin
is recorded separately and explicitly.  The westward velocity component is
negative because positive `x` points east.
-/
structure MatchesProblemReadouts (setup : TwoTravelerMeetingSetup) : Prop where
  chicagoAtMileZero :
    positionInMiles (setup.cityPosition .chicago) = 0
  pittsburghFourHundredMilesEast :
    positionInMiles (setup.cityPosition .pittsburgh) -
        positionInMiles (setup.cityPosition .chicago) = 400
  commonDepartureAtNineAM :
    clockTimeInHours setup.departureTime = 9
  bobVelocityMilesPerHour :
    velocityInMilesPerHour (setup.constantXVelocity .bob) = 60
  susanVelocityMilesPerHour :
    velocityInMilesPerHour (setup.constantXVelocity .susan) = -40

/-!
Qualitative facts and tuple/arrow labels read from the primary raster.  The
image locates a meeting marker between the city endpoints but prints no
numerical meeting coordinate and no answer-choice letter.
-/
structure MatchesSuppliedFigure (setup : TwoTravelerMeetingSetup) : Prop where
  everyLiteralLabelShown : ∀ label, setup.figure.showsLabel label = true
  bothDepartureCarsShown :
    ∀ traveler, setup.figure.carShown traveler .departure = true
  bothMeetingCarsShown :
    ∀ traveler, setup.figure.carShown traveler .meeting = true
  everyStateTupleShown :
    ∀ traveler event, setup.figure.stateTupleShown traveler event = true
  bothCityEndpointsShown :
    ∀ city, setup.figure.cityAtAxisEndpoint city = true
  chicagoDrawnLeftOfPittsburgh :
    setup.figure.cityOrderLeftToRight .chicago .pittsburgh = true
  bothVelocityArrowsShown :
    ∀ traveler, setup.figure.velocityArrowShown traveler = true
  bobArrowPointsEast :
    setup.figure.velocityArrowDirection .bob = .east
  susanArrowPointsWest :
    setup.figure.velocityArrowDirection .susan = .west
  bothZeroAccelerationVectorsShown :
    ∀ traveler, setup.figure.zeroAccelerationVectorShown traveler = true
  bothSetsOfMotionMarkersShown :
    ∀ traveler, setup.figure.motionSampleMarkersShown traveler = true
  meetHereMarkerShown : setup.figure.commonMeetingMarkerShown = true

/-- Sign and time-order conditions selecting the intended physical branch. -/
structure HasPhysicalMeetingParameters
    (setup : TwoTravelerMeetingSetup) : Prop where
  pittsburghIsEastOfChicago :
    positionInMiles (setup.cityPosition .chicago) <
      positionInMiles (setup.cityPosition .pittsburgh)
  bobMovesInPositiveX :
    0 < velocityInMilesPerHour (setup.constantXVelocity .bob)
  susanMovesInNegativeX :
    velocityInMilesPerHour (setup.constantXVelocity .susan) < 0
  meetingOccursAfterDeparture :
    clockTimeInHours setup.departureTime <
      clockTimeInHours setup.meetingTime

/-! ## Governing one-dimensional kinematics -/

/-!
The zero-acceleration law shown by the two `a⃗ = 0⃗` labels.  It is stated in
every coherent choice of length and time units and contains no meeting answer.
-/
structure SatisfiesZeroAccelerationLaw
    (setup : TwoTravelerMeetingSetup) : Prop where
  zeroAcceleration :
    ∀ (traveler : Traveler) (time : ClockTimeQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit
        (setup.xAccelerationAt traveler time) = 0

/-!
Uniform rectilinear motion in any coherent length/time unit system:
`x(t) = x(t₀) + vₓ (t - t₀)`.  This is a general governing law for each
traveler and does not mention the meeting location or any answer choice.
-/
structure SatisfiesUniformMotionLaw
    (setup : TwoTravelerMeetingSetup) : Prop where
  positionFromConstantVelocity :
    ∀ (traveler : Traveler) (time : ClockTimeQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      clockTimeReadout timeUnit setup.departureTime ≤
          clockTimeReadout timeUnit time →
        positionReadout lengthUnit (setup.xPositionAt traveler time) =
          positionReadout lengthUnit
              (setup.xPositionAt traveler setup.departureTime) +
            velocityReadout lengthUnit timeUnit
                (setup.constantXVelocity traveler) *
              (clockTimeReadout timeUnit time -
                clockTimeReadout timeUnit setup.departureTime)

/-!
The designated lunch event occurs after departure and has a single shared
position.  This predicate identifies what “meet” means but does not state
where the event occurs.
-/
def IsMeetingEvent
    (setup : TwoTravelerMeetingSetup) (time : ClockTimeQuantity) : Prop :=
  clockTimeInHours setup.departureTime < clockTimeInHours time ∧
    setup.xPositionAt .bob time = setup.xPositionAt .susan time

/-- The signed displacement of the lunch point east of Chicago, in miles. -/
def meetingDisplacementEastOfChicagoInMiles
    (setup : TwoTravelerMeetingSetup) : ℝ :=
  positionInMiles (setup.xPositionAt .bob setup.meetingTime) -
    positionInMiles (setup.cityPosition .chicago)

/-! ## Multiple-choice data and target relation -/

/-- The four response labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Mile values printed beside the four response labels. -/
def answerChoiceMiles : AnswerChoice → ℝ
  | .A => 220
  | .B => 240
  | .C => 250
  | .D => 230

/--
Bob and Susan meet `240 miles` east of Chicago, which is answer choice B.

Blueprint: `thm:physics:phyx_mini_0830:target`.
-/
theorem meet_two_hundred_forty_miles_east_of_chicago
    (setup : TwoTravelerMeetingSetup)
    (hScenario : MatchesTravelScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalMeetingParameters setup)
    (hZeroAcceleration : SatisfiesZeroAccelerationLaw setup)
    (hUniformMotion : SatisfiesUniformMotionLaw setup)
    (hMeeting : IsMeetingEvent setup setup.meetingTime) :
    meetingDisplacementEastOfChicagoInMiles setup = 240 := by
  rcases hMeeting with ⟨hAfter, hMeet⟩
  have hBob := hUniformMotion.positionFromConstantVelocity
    .bob setup.meetingTime LengthUnit.miles TimeUnit.hours (le_of_lt hAfter)
  have hSusan := hUniformMotion.positionFromConstantVelocity
    .susan setup.meetingTime LengthUnit.miles TimeUnit.hours (le_of_lt hAfter)
  rw [hScenario.bobStartsAtHome, hScenario.bobLivesInChicago] at hBob
  rw [hScenario.susanStartsAtHome, hScenario.susanLivesInPittsburgh] at hSusan
  have hMeetMiles := congrArg positionInMiles hMeet
  change positionReadout LengthUnit.miles
      (setup.xPositionAt .bob setup.meetingTime) =
    positionReadout LengthUnit.miles
      (setup.xPositionAt .susan setup.meetingTime) at hMeetMiles
  have hChicago := hData.chicagoAtMileZero
  have hPittsburgh := hData.pittsburghFourHundredMilesEast
  have hBobV := hData.bobVelocityMilesPerHour
  have hSusanV := hData.susanVelocityMilesPerHour
  change positionReadout LengthUnit.miles
    (setup.cityPosition .chicago) = 0 at hChicago
  change positionReadout LengthUnit.miles (setup.cityPosition .pittsburgh) -
    positionReadout LengthUnit.miles
      (setup.cityPosition .chicago) = 400 at hPittsburgh
  change velocityReadout LengthUnit.miles TimeUnit.hours
    (setup.constantXVelocity .bob) = 60 at hBobV
  change velocityReadout LengthUnit.miles TimeUnit.hours
    (setup.constantXVelocity .susan) = -40 at hSusanV
  rw [hBobV] at hBob
  rw [hSusanV] at hSusan
  norm_num at hBob hSusan
  unfold meetingDisplacementEastOfChicagoInMiles positionInMiles
  linarith

end PhyXMiniProblems.ProblemPhyXMini0830
