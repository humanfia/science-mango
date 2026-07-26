import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Speed

/-!
# Spermaceti-sac length from the interval between whale clicks

This file formalizes problem `phyx_mini_0321`.  The first click escapes near
the distal sac.  The sound producing the second click travels from the distal
sac through the spermaceti sac, reflects at the frontal sac, and returns to the
distal sac.  Thus adjacent clicks are separated by the travel time for two sac
lengths.

The primary figure's `1.0 ms` scale bar fits three times between corresponding
peaks of adjacent clicks, so the measured interval is `3.0 ms`.  At
`1372 m/s`, the exact model length is `2.058 m`; this agrees with the displayed
one-decimal answer `2.1 m` without treating that rounded answer as exact.

Physical lengths, durations, and speeds use Physlib's unit-independent
`Dimensionful` quantities.  Real numbers occur only as readouts in explicitly
selected units and as dimensionless chart or answer data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0321

open Dimension

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical elapsed time, independent of the readout unit. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : AcousticDuration) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in compatible selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout used for sac and path lengths in the problem. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used for the click-chart timing data. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Meters-per-second readout used for the stated sound speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Figure labels and click routes -/

/-- The two air-layer boundaries labeled in the whale-head diagram. -/
inductive SacBoundary where
  | distalSac
  | frontalSac
  deriving DecidableEq, Repr

/-- The propagation medium labeled `Spermaceti sac` in the diagram. -/
inductive PropagationMedium where
  | spermacetiSac
  deriving DecidableEq, Repr

/-- A sound route through a medium from a boundary to a reflector and back. -/
structure EchoRoute where
  startsAt : SacBoundary
  medium : PropagationMedium
  reflectsAt : SacBoundary
  returnsTo : SacBoundary
  deriving DecidableEq, Repr

/-- How a particular chart click is formed. -/
inductive ClickMechanism where
  | directEscape (atBoundary : SacBoundary)
  | afterRoundTrip (route : EchoRoute)
  deriving DecidableEq, Repr

/-!
The physical quantities and chart roles for the sperm-whale experiment.
`spermacetiSacLength` is the requested unknown and has no numerical value in
this structure.  `echoRoundTripDistance` is kept as a separate physical length
so geometry and constant-speed travel can be stated as distinct laws.
-/
structure SpermWhaleClickSetup where
  spermacetiSacLength : AcousticLength
  echoRoundTripDistance : AcousticLength
  soundSpeedInSac : DimSpeed
  chartUnitInterval : AcousticDuration
  adjacentClickInterval : AcousticDuration
  chartUnitBarsBetweenAdjacentClicks : ℕ
  echoRoute : EchoRoute
  firstClickMechanism : ClickMechanism
  secondClickMechanism : ClickMechanism

/-!
The stated numerical data and the readouts from the primary figure.  The
`1.0 ms` scale bar spans one third of the interval between corresponding click
peaks.  This predicate fixes no value for the requested sac length or for the
round-trip distance.
-/
structure MatchesProblemAndFigure (setup : SpermWhaleClickSetup) : Prop where
  sound_speed_meters_per_second :
    speedInMetersPerSecond setup.soundSpeedInSac = 1372
  chart_unit_interval_seconds :
    durationInSeconds setup.chartUnitInterval = 1 / 1000
  chart_bars_between_adjacent_clicks :
    setup.chartUnitBarsBetweenAdjacentClicks = 3
  adjacent_click_interval_from_chart :
    durationInSeconds setup.adjacentClickInterval =
      setup.chartUnitBarsBetweenAdjacentClicks *
        durationInSeconds setup.chartUnitInterval
  route_starts_at_distal_sac : setup.echoRoute.startsAt = .distalSac
  route_medium_is_spermaceti_sac : setup.echoRoute.medium = .spermacetiSac
  route_reflects_at_frontal_sac : setup.echoRoute.reflectsAt = .frontalSac
  route_returns_to_distal_sac : setup.echoRoute.returnsTo = .distalSac
  first_click_escapes_directly :
    setup.firstClickMechanism = .directEscape .distalSac
  second_click_follows_round_trip :
    setup.secondClickMechanism = .afterRoundTrip setup.echoRoute

/-- Strict positivity conditions for the physical branch of the model. -/
structure HasPhysicalParameters (setup : SpermWhaleClickSetup) : Prop where
  sac_length_positive : 0 < lengthInMeters setup.spermacetiSacLength
  round_trip_distance_positive :
    0 < lengthInMeters setup.echoRoundTripDistance
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeedInSac
  chart_unit_interval_positive :
    0 < durationInSeconds setup.chartUnitInterval
  adjacent_click_interval_positive :
    0 < durationInSeconds setup.adjacentClickInterval

/-!
The governing geometry and acoustics laws.  The echo route has two legs, each
the length of the spermaceti sac, and propagation at constant speed obeys
`distance = speed * time`.  Both relations are required in every compatible
choice of length and time units; neither contains the requested numerical
answer.
-/
structure SatisfiesEchoRoundTripLaws (setup : SpermWhaleClickSetup) : Prop where
  round_trip_has_two_sac_legs : ∀ lengthUnit,
    lengthReadout lengthUnit setup.echoRoundTripDistance =
      2 * lengthReadout lengthUnit setup.spermacetiSacLength
  constant_speed_travel : ∀ lengthUnit timeUnit,
    lengthReadout lengthUnit setup.echoRoundTripDistance =
      speedReadout lengthUnit timeUnit setup.soundSpeedInSac *
        durationReadout timeUnit setup.adjacentClickInterval

/-! ## Derived length and displayed answer -/

/-- The general round-trip formula, before inserting this figure's numbers. -/
lemma spermacetiSacLength_formula
    (setup : SpermWhaleClickSetup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesEchoRoundTripLaws setup) :
    lengthInMeters setup.spermacetiSacLength =
      speedInMetersPerSecond setup.soundSpeedInSac *
          durationInSeconds setup.adjacentClickInterval /
        2 := by
  have hgeometry :=
    _laws.round_trip_has_two_sac_legs LengthUnit.meters
  have htravel :=
    _laws.constant_speed_travel LengthUnit.meters TimeUnit.seconds
  unfold lengthInMeters speedInMetersPerSecond durationInSeconds
  linarith

/-- Labels of the four lengths displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter readout printed beside each displayed answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 34 / 10
  | .B => 29 / 10
  | .C => 25 / 10
  | .D => 21 / 10

/-!
A physical length agrees with a one-decimal-place displayed answer.  The
`0.05 m` tolerance is half of the displayed `0.1 m` increment.
-/
def MatchesAnswerChoice
    (length : AcousticLength) (choice : AnswerChoice) : Prop :=
  |lengthInMeters length - choice.meters| ≤ 1 / 20

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The three-millisecond echo interval and the sound speed `1372 m/s` give the
exact sac length `2.058 m = 1029/500 m`.  This lies within `0.05 m` of the
displayed `2.1 m` choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0321:target`.
-/
theorem spermacetiSacLength_matches_recordedAnswerD
    (setup : SpermWhaleClickSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesEchoRoundTripLaws setup) :
    lengthInMeters setup.spermacetiSacLength = 1029 / 500 ∧
      MatchesAnswerChoice setup.spermacetiSacLength recordedAnswerChoice := by
  have htime :
      durationInSeconds setup.adjacentClickInterval = 3 / 1000 := by
    rw [_problem.adjacent_click_interval_from_chart,
      _problem.chart_bars_between_adjacent_clicks,
      _problem.chart_unit_interval_seconds]
    norm_num
  have hlength := spermacetiSacLength_formula setup _physical _laws
  rw [_problem.sound_speed_meters_per_second, htime] at hlength
  constructor
  · norm_num at hlength ⊢
    exact hlength
  · norm_num at hlength
    unfold MatchesAnswerChoice
    rw [hlength]
    norm_num [recordedAnswerChoice, AnswerChoice.meters, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0321
