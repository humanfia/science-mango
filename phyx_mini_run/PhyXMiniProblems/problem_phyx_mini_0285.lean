import Mathlib.Algebra.Order.Round
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0285

open Dimension

/-!
# Width of a stadium human wave

A human wave travels around a stadium while each spectator remains active from
the instant the leading edge arrives until the trailing edge passes.  Length
readouts use one seat spacing as the stadium's length unit, time readouts use
seconds, and speed readouts therefore use seat spacings per second.

The continuous pulse width need not be an integer.  The requested answer in
"number of seats" is represented by Mathlib's nearest-integer `round` of its
seat-spacing readout.  The theorem below says this rounded width is `39`, which
is answer choice D.
-/

/-! ## Dimensionful physical quantities -/

/-- A stadium distance or one-dimensional edge coordinate. -/
abbrev LengthQuantity : Type := WithDim L𝓭 ℝ

/-- A duration, whose scalar readout is measured in seconds. -/
abbrev TimeQuantity : Type := WithDim T𝓭 ℝ

/-- A propagation speed, whose scalar readout is measured in seat spacings per second. -/
abbrev SpeedQuantity : Type := WithDim (L𝓭 * T𝓭⁻¹) ℝ

/-! ## Physical and figure labels -/

/-- The state of spectators at either boundary of the moving pulse. -/
inductive SpectatorBoundaryState where
  /-- Spectators at the leading edge are just about to stand. -/
  | aboutToStand
  /-- Spectators at the trailing edge have just sat down. -/
  | justSatDown
  deriving DecidableEq, Repr

/-- The propagation direction shown by the arrow labelled `v`. -/
inductive PropagationDirection where
  | rightward
  deriving DecidableEq, Repr

/-- Symbols printed on the two arrows in the source figure. -/
inductive FigureLabel where
  | v
  | w
  deriving DecidableEq, Repr

/-- The two annotated features in the source figure. -/
inductive FigureFeature where
  | propagationArrow
  | widthSpan
  deriving DecidableEq, Repr

/-- The width annotation is a two-ended span rather than a direction of travel. -/
inductive WidthMarkerKind where
  | doubleEndedSpan
  deriving DecidableEq, Repr

/-- A structured transcription of the primary image. -/
structure SourceFigure where
  labelOf : FigureFeature → FigureLabel
  propagationArrowDirection : PropagationDirection
  widthMarkerKind : WidthMarkerKind
  widthLeftEndpoint : LengthQuantity
  widthRightEndpoint : LengthQuantity
  visibleSpectatorCount : ℕ

/-! ## Human-wave setup -/

/--
The physical quantities of the stadium pulse.

`waveWidth` is independent data in the structure: it is not defined as the
requested numerical answer.  Its relationship to the edges and to the response
duration is supplied separately by the governing-law predicate.
-/
structure StadiumHumanWave where
  travelDistance : LengthQuantity
  travelTime : TimeQuantity
  spectatorResponseDuration : TimeQuantity
  waveSpeed : SpeedQuantity
  trailingEdgeCoordinate : LengthQuantity
  leadingEdgeCoordinate : LengthQuantity
  waveWidth : LengthQuantity
  leadingEdgeState : SpectatorBoundaryState
  trailingEdgeState : SpectatorBoundaryState
  propagationDirection : PropagationDirection
  figure : SourceFigure

/-! ## Governing laws -/

/-- The dimensionally typed constant-speed relation `v = d / t`. -/
def SatisfiesSpeedDistanceTimeLaw (setup : StadiumHumanWave) : Prop :=
  setup.waveSpeed = WithDim.cast (setup.travelDistance / setup.travelTime)

/-- During the response interval, the pulse advances by one pulse width: `w = v Δt`. -/
def SatisfiesWidthResponseLaw (setup : StadiumHumanWave) : Prop :=
  setup.waveWidth =
    WithDim.cast (setup.waveSpeed * setup.spectatorResponseDuration)

/-- The width `w` is the separation from the trailing edge to the leading edge. -/
def SatisfiesEdgeSeparationLaw (setup : StadiumHumanWave) : Prop :=
  setup.waveWidth = setup.leadingEdgeCoordinate - setup.trailingEdgeCoordinate

/-- The physical laws used to infer the pulse width; no numerical answer occurs here. -/
structure HasHumanWavePhysics (setup : StadiumHumanWave) : Prop where
  speedDistanceTime : SatisfiesSpeedDistanceTimeLaw setup
  widthFromResponseTime : SatisfiesWidthResponseLaw setup
  widthIsEdgeSeparation : SatisfiesEdgeSeparationLaw setup

/-! ## Stated measurements and primary-image readout -/

/--
The numerical measurements and boundary meanings stated in the problem.
The exact rational `9 / 5` is the `1.8 s` response-time readout.
-/
structure MatchesProblemData (setup : StadiumHumanWave) : Prop where
  travelDistanceSeatSpacings : setup.travelDistance.val = 853
  travelTimeSeconds : setup.travelTime.val = 39
  responseTimeSeconds : setup.spectatorResponseDuration.val = 9 / 5
  travelDistancePositive : 0 < setup.travelDistance.val
  travelTimePositive : 0 < setup.travelTime.val
  responseTimePositive : 0 < setup.spectatorResponseDuration.val
  leadingBoundaryMeaning : setup.leadingEdgeState = .aboutToStand
  trailingBoundaryMeaning : setup.trailingEdgeState = .justSatDown

/--
The figure shows six spectators, a rightward arrow labelled `v`, and a width
span labelled `w` whose endpoints coincide with the pulse edges.
-/
structure MatchesSourceFigure (setup : StadiumHumanWave) : Prop where
  physicalDirection : setup.propagationDirection = .rightward
  speedArrowLabel : setup.figure.labelOf .propagationArrow = .v
  widthSpanLabel : setup.figure.labelOf .widthSpan = .w
  speedArrowPointsRight : setup.figure.propagationArrowDirection = .rightward
  widthIsDoubleEndedSpan : setup.figure.widthMarkerKind = .doubleEndedSpan
  widthLeftEndpoint : setup.figure.widthLeftEndpoint = setup.trailingEdgeCoordinate
  widthRightEndpoint : setup.figure.widthRightEndpoint = setup.leadingEdgeCoordinate
  sixSpectatorsVisible : setup.figure.visibleSpectatorCount = 6

/-! ## Current target -/

/--
For a wave that covers `853` seat spacings in `39 s`, with a spectator response
duration of `1.8 s`, the nearest whole-seat width is `39` seats (choice D).

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0285:target`.
-/
theorem rounded_width_is_thirty_nine_seats
    (setup : StadiumHumanWave)
    (_data : MatchesProblemData setup)
    (_figure : MatchesSourceFigure setup)
    (_physics : HasHumanWavePhysics setup) :
    round setup.waveWidth.val = 39 := by
  have hspeed := congrArg WithDim.val _physics.speedDistanceTime
  change setup.waveSpeed.val =
    setup.travelDistance.val / setup.travelTime.val at hspeed
  have hwidth := congrArg WithDim.val _physics.widthFromResponseTime
  change setup.waveWidth.val =
    setup.waveSpeed.val * setup.spectatorResponseDuration.val at hwidth
  rw [hwidth, hspeed, _data.travelDistanceSeatSpacings, _data.travelTimeSeconds,
    _data.responseTimeSeconds, round_eq_iff]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0285
