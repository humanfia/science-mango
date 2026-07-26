# Autoformalization result: `problem_phyx_mini_0829.lean`

This is the genuine post-formalization report requested by review 3. I audited
the current Lean file against the current source report, the primary image
`phyx_data/test_image/829.png`, and the blueprint chapter. The review-gate
reason is evidence-only, and the audit found no semantic defect, so the Lean
declarations were deliberately preserved rather than redrafted.

The chapter contains `% archon:physics`; the physics-formalize discipline was
therefore applied.

## Physical model extracted

- `SignedPositionQuantity` and `SignedDisplacementQuantity` are
  unit-independent signed quantities of Physlib length dimension `L𝓭`.
- `TimeCoordinateQuantity` is a unit-independent signed time coordinate of
  dimension `T𝓭`; `DurationQuantity` has the same dimension but uses `NNReal`
  so elapsed time is nonnegative.
- `SignedVelocityQuantity` is a signed one-dimensional component with dimension
  `L𝓭 * T𝓭⁻¹`.
- The named SI projections read position/displacement in metres, time/duration
  in seconds, and velocity in metres per second via `UnitChoices.SI`.
- The primary figure has horizontal time and vertical x-position axes, labels
  `t (s)` and `x (m)`, students A and B, straight traces, and respectively
  increasing/decreasing trends.
- The primary image shows A from `(0 s, 2 m)` to `(0.40 s, 4 m)`, with displayed
  `Delta t_A = 0.40 s` and `Delta x_A = 2.0 m`. It shows B from `(0 s, 1 m)` to
  `(0.50 s, 0 m)`, with `Delta t_B = 0.50 s` and `Delta x_B = -1.0 m`.
- The governing kinematic relation is signed velocity equals signed
  displacement divided by a nonzero elapsed time on each straight
  position-time trace.
- The requested conclusion is A's signed x-velocity `5 m/s`, together with the
  fact that recorded answer label B is the unique displayed match.

## Assumption/target split

### Governing laws

- `SatisfiesPositionTimeGraphVelocityLaw.displayedIntervalsAreNonzero` requires
  each displayed interval to have nonzero duration.
- `SatisfiesPositionTimeGraphVelocityLaw.velocityIsGraphSlope` states, uniformly
  for both students, that the SI velocity readout is the displayed signed
  displacement divided by the displayed elapsed time. It contains no evaluated
  numerical velocity and no answer-label selection.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesRollerBladeScenario` records the participants' roller-blading role.
- `MatchesSuppliedPositionTimeFigure` records axes, units, literal labels,
  ticks, student labels, straight-line geometry, trends, trajectory endpoints,
  displayed elapsed times/displacements, and the qualitative slope-formula
  annotation.
- A's independent finite-difference data are `0.40 s = 2/5 s` and `2 m`; B's
  are `0.50 s = 1/2 s` and `-1 m`.
- `AnswerChoice.displayedMetersPerSecond` and `recordedAnswerChoice` transcribe
  the option list and the dataset's recorded label. They do not constrain the
  setup's physical velocity.

### Current target conclusions

- `velocityInMetersPerSecond (setup.velocityX .A) = 5`.
- `IsUniqueMatchingStudentAVelocityChoice setup recordedAnswerChoice`.

## Goal-faithfulness audit

The current target is not a field of `RollerBladeMotionSetup`,
`MatchesRollerBladeScenario`, `MatchesSuppliedPositionTimeFigure`, or
`SatisfiesPositionTimeGraphVelocityLaw`. In particular, the image's printed
evaluated A-slope `5.0 m/s` is intentionally omitted from the premise
structures even though it is visible in blue; only the independent delta
readouts and the non-numerical slope annotation are premise data.

The general law is stated for every student and becomes numerical only after
combining it with the figure readouts. The option table necessarily contains
B's displayed value `5`, but it is answer-list metadata: neither the setup nor
the law is defined from that table. `MatchesStudentAVelocityChoice` still
requires equality between an independently modeled physical observable and an
option value, and `IsUniqueMatchingStudentAVelocityChoice` additionally
requires uniqueness. Thus unfolding the target-side predicates does not make
the theorem true without the figure data and governing law.

No premise, local helper definition, or physics-validity structure assigns
student A's velocity to `5`. Both substantive proof bodies remain `by sorry`,
as required for autoformalization.

## Declarations and blueprint labels

No public declaration was added, removed, renamed, or retyped in this
evidence-only retry. The current file's declarations correspond to the chapter
as follows:

- Quantity types:
  - `SignedPositionQuantity` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-signedpositionquantity`
  - `SignedDisplacementQuantity` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-signeddisplacementquantity`
  - `TimeCoordinateQuantity` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-timecoordinatequantity`
  - `DurationQuantity` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-durationquantity`
  - `SignedVelocityQuantity` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-signedvelocityquantity`
- Coherent/SI readouts:
  - `positionReadout`, `displacementReadout`, `timeReadout`, `durationReadout`,
    `velocityReadout` — the five corresponding labels ending in
    `positionreadout`, `displacementreadout`, `timereadout`, `durationreadout`,
    and `velocityreadout`.
  - `positionInMeters`, `displacementInMeters`, `timeInSeconds`,
    `durationInSeconds`, `velocityInMetersPerSecond` — the five corresponding
    labels ending in `positioninmeters`, `displacementinmeters`,
    `timeinseconds`, `durationinseconds`, and `velocityinmeterspersecond`.
- Figure vocabulary:
  - `Student`, `ParticipantKind`, `GraphAxis`, `AxisQuantity`, `AxisUnit`,
    `TraceGeometry`, `TraceTrend`, `SlopeAnnotation` — the corresponding labels
    ending in `student`, `participantkind`, `graphaxis`, `axisquantity`,
    `axisunit`, `tracegeometry`, `tracetrend`, and `slopeannotation`.
- Physical model and evidence:
  - `PositionTimeGraphFigure` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-positiontimegraphfigure`
  - `RollerBladeMotionSetup` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-rollerblademotionsetup`
  - `MatchesRollerBladeScenario` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-matchesrollerbladescenario`
  - `MatchesSuppliedPositionTimeFigure` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-matchessuppliedpositiontimefigure`
  - `SatisfiesPositionTimeGraphVelocityLaw` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-satisfiespositiontimegraphvelocitylaw`
  - `studentA_finiteDifference_readouts` — `lem:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-studenta-finitedifference-readouts`
- Answer metadata and matching:
  - `AnswerChoice` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-answerchoice`
  - `AnswerChoice.displayedMetersPerSecond` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-answerchoice-displayedmeterspersecond`
  - `recordedAnswerChoice` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-recordedanswerchoice`
  - `MatchesStudentAVelocityChoice` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-matchesstudentavelocitychoice`
  - `IsUniqueMatchingStudentAVelocityChoice` — `def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-isuniquematchingstudentavelocitychoice`
- Target theorem:
  - `studentA_velocity_is_five_meters_per_second` — `thm:physics:phyx_mini_0829:target`

All abbreviated label suffixes above have the common prefix
`def:physics:phyx-mini-0829:phyxminiproblems-problemphyxmini0829-`, exactly as
written in the blueprint.

## LeanExplore queries and candidates actually used

Every search in this iteration passed `packages: ["Mathlib", "Physlib"]`.
The exact queries were:

- Natural language: `dimensionful physical quantities with units of length time and velocity`
- Likely names: `Dimensionful WithDim UnitChoices.SI`
- Natural language: `Time physical time coordinate arbitrary units and origin`
- Natural language: `velocity equals displacement divided by elapsed time position time graph`
- Likely name: `WithDim`
- Likely name: `Dimension.T𝓭`
- Natural language/name combination: `NNReal nonnegative real`

The adopted candidates were `Dimensionful` (LeanExplore id `394284`),
`WithDim` (`394425`), `UnitChoices.SI` (`394270`), `Dimension.L𝓭`
(`394324`), `Dimension.T𝓭` (`394330`), and `NNReal` (`211536`). Source,
module, and docstring were fetched for each adopted candidate.

The relevant source/module facts were:

- `Dimensionful` is the Physlib subtype of unit-choice-indexed values satisfying
  dimensional scaling, in `Physlib.Units.Basic`.
- `WithDim` tags an underlying type with a `Dimension`, in
  `Physlib.Units.WithDim.Basic`.
- `UnitChoices.SI` chooses metres, seconds, kilograms, coulombs, and kelvin, in
  `Physlib.Units.Basic`.
- `Dimension.L𝓭` and `Dimension.T𝓭` are the length and time dimensions, in
  `Physlib.Units.Dimension`.
- Mathlib's `NNReal` is the subtype of nonnegative real numbers, in
  `Mathlib.Data.NNReal.Defs`.

The searches also returned Physlib `Time`, `RigidBodyMotion.velocity`,
`RigidBodyMotion.displacement`, and several specialized trajectory velocities.
They were reviewed but not adopted: `Time` would not by itself give the unified
dimensionful position/displacement/velocity model used here, while the
rigid-body and oscillator APIs are specialized to different physical systems.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`,
  `Dimension`, `Dimension.L𝓭`, and `Dimension.T𝓭`.
- Mathlib: `NNReal`, `ℝ`, `List`, and standard finite inductive/decidable
  infrastructure supplied by `Mathlib`.

## Local abstractions introduced and retained

- The five named kinematic quantity types are semantic abbreviations of
  Physlib dimensional objects, not transparent scalar aliases. Their dimensions
  and signed/nonnegative carrier distinctions preserve physical meaning.
- `PositionTimeGraphFigure` is a typed transcription of the graph, separating
  physical quantities from their real-valued SI readouts.
- `RollerBladeMotionSetup` separates trajectories and physical velocity
  observables from figure evidence and answer metadata.
- `SatisfiesPositionTimeGraphVelocityLaw` is the smallest local law interface
  for this elementary straight position-time graph.
- The local enums preserve participant labels, axis roles/units, straight-line
  geometry, trace trend, answer labels, and the qualitative slope annotation.

## Grounding gaps and redraft requests

- LeanExplore exposed no purpose-built Mathlib/Physlib declaration for a signed
  one-dimensional velocity component computed from a finite interval of a
  position-time graph. The local uniform slope-law interface faithfully fills
  that gap without assuming the evaluated answer.
- The source caption's claim that student B starts near `t = 0.6 s` conflicts
  with the primary bitmap. The bitmap clearly shows B starting at `(0 s, 1 m)`
  and reaching `0 m` after `0.50 s`; the formalization correctly follows the
  chapter's instruction to treat the image as primary evidence.
- The `archon` executable advertised for DAG navigation is not available on
  this process's `PATH`; both `dag-query node` and `dag-query ancestors`
  attempts returned `command not found`. This does not affect the declaration
  audit or compilation.
- The requested current `.archon/AGENTS.md` is absent. A read-only archived
  review-3 copy was used only to recover prover-role guidance; the current
  prompt and current `PROGRESS.md` remained authoritative.
- No redraft is requested. The chapter exists and contains `% archon:physics`.
  It was not edited because prover write permissions prohibit blueprint edits;
  the declarations are ready for deterministic `\leanok` synchronization.

## Verification

- `archon-lean-lsp` diagnostics succeeded with no errors and exactly two
  expected `declaration uses sorry` warnings, at the helper lemma and target
  theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0829.lean` exited `0` with
  exactly the same two expected warnings.
