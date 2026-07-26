# Autoformalization result: `problem_phyx_mini_0830.lean`

## Assumption/target split

### Governing laws

- `SatisfiesZeroAccelerationLaw.zeroAcceleration` expresses the figure's two
  zero-acceleration vectors in every coherent length/time unit choice.
- `SatisfiesUniformMotionLaw.positionFromConstantVelocity` expresses
  `x(t) = x(t₀) + vₓ (t - t₀)` for both travelers after departure, in every
  coherent length/time unit choice.
- `IsMeetingEvent` identifies the designated later lunch event by strict time
  order and equality of Bob's and Susan's physical positions. It does not give
  the common position.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesTravelScenario` records Bob/Susan, Chicago/Pittsburgh, simultaneous
  departure through the shared `departureTime`, east/west directions, initial
  positions at their respective homes, and the constant-velocity motion
  regime.
- `MatchesProblemReadouts` records Chicago as mile zero, Pittsburgh 400 miles
  east of Chicago, departure at 9:00 A.M., Bob's signed velocity as `+60 mph`,
  and Susan's as `-40 mph`.
- `MatchesSuppliedFigure` records the horizontal `x` axis, city and traveler
  labels, both initial/final `(x, vₓ, t)` tuples, opposing velocity arrows,
  zero-acceleration labels, motion markers, and the “Meet here” marker.
- `HasPhysicalMeetingParameters` records the intended spatial, velocity-sign,
  and temporal branch.
- `AnswerChoice` and `answerChoiceMiles` transcribe A = 220, B = 240,
  C = 250, and D = 230 miles. These are response data and are not referenced
  by any premise of the target theorem.

### Current target conclusions

- `meet_two_hundred_forty_miles_east_of_chicago` concludes
  `meetingDisplacementEastOfChicagoInMiles setup = 240`, corresponding to
  recorded answer choice B.

## Goal-faithfulness audit

- No hypothesis or setup field states the meeting coordinate, the 240-mile
  displacement, or the correct answer label.
- `meetingTime` is an independent physical clock time. `IsMeetingEvent` only
  constrains the two positions to be equal there and requires it to be later
  than departure.
- `meetingDisplacementEastOfChicagoInMiles` only subtracts Chicago's mile
  readout from Bob's position at the meeting time; it contains no numeric
  answer.
- `answerChoiceMiles` contains the printed multiple-choice table, but the
  target theorem does not use that definition as a hypothesis or unfold it to
  manufacture the physical conclusion.
- The 400-mile separation and signed velocities are input measurements, while
  the 240-mile result remains exclusively on the theorem's conclusion side.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0830:target` corresponds to Lean
  theorem
  `PhyXMiniProblems.ProblemPhyXMini0830.meet_two_hundred_forty_miles_east_of_chicago`.
- Quantity/readout declarations: `SignedPositionQuantity`,
  `ClockTimeQuantity`, `SignedVelocityQuantity`,
  `SignedAccelerationQuantity`, `positionReadout`, `clockTimeReadout`,
  `velocityReadout`, and `accelerationReadout` plus named mile/hour readouts.
- Physical/figure declarations: `Traveler`, `City`, `AxisDirection`,
  `FigureEvent`, `MotionRegime`, `FigureLabel`,
  `ChicagoPittsburghMeetingFigure`, and `TwoTravelerMeetingSetup`.
- Premise declarations: `MatchesTravelScenario`, `MatchesProblemReadouts`,
  `MatchesSuppliedFigure`, `HasPhysicalMeetingParameters`,
  `SatisfiesZeroAccelerationLaw`, `SatisfiesUniformMotionLaw`, and
  `IsMeetingEvent`.
- Target helper/data declarations: `meetingDisplacementEastOfChicagoInMiles`,
  `AnswerChoice`, and `answerChoiceMiles`.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Query `dimensionful physical length quantity with units`: selected
  `Dimensionful` (ID 394284), module `Physlib.Units.Basic`.
- Query `physical velocity dimension length divided by time`: selected
  `Dimension.L𝓭`, `Dimension.T𝓭`, and dimension multiplication/inversion
  for the signed velocity and acceleration quantity dimensions. The search
  also returned `UnitExamples.SpeedEq` (ID 394344); its fetched source confirms
  the dimension `L𝓭 * T𝓭⁻¹`.
- Query `length unit miles and time unit hours`: selected `LengthUnit.miles`
  (ID 393169) and led to the exact `TimeUnit.hours` query.
- Query `TimeUnit.hours`: selected `TimeUnit.hours` (ID 393639), module
  `Physlib.SpaceAndTime.Time.TimeUnit`.
- Query `DimSpeed`: inspected `DimSpeed` (ID 394481), module
  `Physlib.Units.WithDim.Speed`.
- Query `constant velocity position equals initial position plus velocity
  times elapsed time`: returned
  `ClassicalMechanics.FreeParticle.velocity_const_of_zero_acc` and related
  free-particle results, but no directly compatible signed one-dimensional,
  arbitrary-unit position law was selected.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.miles`, `TimeUnit`,
  and `TimeUnit.hours`.
- `DimSpeed` and `DimSpeed.oneMilePerHour` were inspected but intentionally not
  used because `DimSpeed` is nonnegative, whereas this figure requires Susan's
  signed westward `x`-velocity component.
- Mathlib's `ℝ` supplies scalar readouts only; the underlying physical
  quantities remain unit-independent Physlib values.

## Local abstractions introduced

- Signed dimensionful position, clock-time, velocity-component, and
  acceleration-component aliases specialize Physlib's `Dimensionful
  (WithDim ... ℝ)` rather than collapsing physical quantities to scalars.
- `ChicagoPittsburghMeetingFigure` preserves literal figure roles and labels
  without inserting a numerical lunch location.
- `TwoTravelerMeetingSetup` keeps physical observables independent.
- Local zero-acceleration and uniform-motion law structures preserve the exact
  one-dimensional physical laws needed by the problem while allowing coherent
  unit readouts.

## Grounding gaps

- LeanExplore did not expose a ready-made API with the exact combination of
  signed one-dimensional position, signed velocity component, physical clock
  time, and arbitrary coherent mile/hour readouts needed here. The local law
  interfaces therefore state that model directly.
- `UnitExamples.SpeedEq` is only a dimensional-consistency example on
  `WithDim` values, not a unit-independent two-trajectory meeting model.
- The requested `.archon/AGENTS.md` file was absent. The available
  `.archon/prover-modes/physics-formalize.md` was read and followed instead.

## Verification and redraft requests

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0830.lean` exits 0 with
  exactly the expected single `declaration uses sorry` warning.
- `archon-lean-lsp` likewise reports only that expected warning and no failed
  dependencies.
- The blueprint chapter was not edited to add `\\leanok`, because the task's
  explicit write-permission section permits edits only to the assigned Lean
  file and this result file and explicitly forbids blueprint edits. The
  orchestrator/plan agent should add `\\leanok` to
  `thm:physics:phyx_mini_0830:target` when permitted.

