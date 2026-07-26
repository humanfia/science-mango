# Autoformalization result: `problem_phyx_mini_0205.lean`

## Retry review response (Archon iteration 002)

- The formalization-review gate requested a genuine post-formalization result;
  its exact reason was that the earlier physics-grounding preflight could not
  evidence the searches and modeling decisions used by the completed Lean
  statement. This report records the actual post-formalization
  assumption/target audit, LeanExplore candidates, local abstractions,
  grounding gaps, source/image checks, and compilation results.
- The retry reason identified an evidence gap, not a defect in the dimensional
  Lean statement. The complete statement was therefore retained and
  revalidated rather than weakened or replaced with a different model.

## Assumption/target split

### Governing laws

- `SatisfiesDivingBoardContactLaws.angularFrequencyConversion` states
  `ω = 2πf`, with separate dimensionful cyclic- and angular-frequency roles.
- `harmonicDisplacementLaw` and `harmonicAccelerationLaw` state the prescribed
  vertical SHM relations `y(t) = A cos (ωt)` and `a(t) = -ω²y(t)`.
- `constrainedMotionLaw` states that a pebble which remains in contact has the
  board end's acceleration.
- `verticalNewtonSecondLaw` states `N - mg = ma` in the upward-positive sign
  convention. `requiredNormalForce` is the force needed for constrained
  co-motion, not a pre-assumed contact-preserving force.
- `upperTurningTimeIsOrigin` identifies a time at the upper turning point so
  the converse/maximality argument can evaluate the most downward
  acceleration.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesDivingBoardFigure` records the qualitative primary-image content
  relevant to the calculation: the contact body is at the board's free end,
  the motion axis is vertical, and signed components use upward positive. The
  image supplies no numerical amplitude or length.
- Direct inspection of `phyx_data/test_image/205.png` confirms a raised board
  extending over a pool and a small light-colored body at its free end. It
  provides no scale, amplitude marker, or numerical apparatus readout; the
  auxiliary caption's identification of that body as a cat is not used as a
  dynamical premise for the source problem's pebble.
- `HasDivingBoardProblemData` records the stated `2.8 cycles/s`, the explicit
  conventional terrestrial gravity readout `9.8 m/s²`, and positive pebble
  mass.
- `AmplitudeAnswerChoice` and `amplitudeAnswerChoiceInMeters` preserve all four
  displayed numerical choices: A = `4.2×10⁻²`, B = `3.2×10⁻³`,
  C = `2.2×10⁻²`, and D = `3.2×10⁻²` meters.

### Current target conclusions

- `maximumDivingBoardAmplitude` concludes the existence of a greatest
  contact-preserving physical amplitude.
- Its meter readout is concluded to equal both `g/ω²` and `g/(2πf)²`.
- The same theorem concludes that the exact value is within `5×10⁻⁴ m` of
  choice D and that D is closest among all four displayed choices.

## Goal-faithfulness audit

- `DivingBoardPebbleSetup` contains amplitude-indexed trajectories,
  accelerations, and required normal forces, but no distinguished maximum
  amplitude and no answer-choice value.
- `MatchesDivingBoardFigure` contains only qualitative placement/orientation;
  it contains no amplitude readout.
- `HasDivingBoardProblemData` contains the problem's independent frequency,
  the conventional gravity constant needed for numerical evaluation, and
  mass positivity. It contains neither `g/ω²` nor `3.2×10⁻²`.
- `SatisfiesDivingBoardContactLaws` contains only generic SHM, constrained
  co-motion, angular-frequency conversion, and Newton-law relations. No field
  states an amplitude threshold or requested maximum.
- `PreservesPebbleContact` says physically that the required unilateral
  normal force is nonnegative throughout the motion. It does not unfold to an
  `A ≤ g/ω²` inequality.
- `IsMaximumContactPreservingAmplitude` is the generic order-theoretic
  greatest-element condition. It supplies no closed form or numerical value.
- Answer-choice definitions merely transcribe displayed data. The conclusion
  still requires deriving the exact maximum from the laws, estimating `π`,
  and comparing all choices. Thus the current answer first appears on the
  theorem's conclusion side.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0205:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0205.maximumDivingBoardAmplitude`.
- Dimensional declarations: `LengthQuantity`, `TimeQuantity`,
  `CyclicFrequencyQuantity`, `AngularFrequencyQuantity`, `MassQuantity`,
  `AccelerationQuantity`, `ForceQuantity`, and their seven named SI readouts.
- Figure/answer vocabulary: `BoardPoint`, `MotionAxis`,
  `VerticalPositiveDirection`, `AmplitudeAnswerChoice`, and
  `amplitudeAnswerChoiceInMeters`.
- Physical model declarations: `DivingBoardPebbleSetup`,
  `MatchesDivingBoardFigure`, `HasDivingBoardProblemData`,
  `SatisfiesDivingBoardContactLaws`, `PreservesPebbleContact`, and
  `IsMaximumContactPreservingAmplitude`.
- The chapter was not edited because the later explicit write-permission block
  permits writes only to the assigned Lean file and this task-result file.
  The target environment is ready for a blueprint-authorized process to add
  `\lean{PhyXMiniProblems.ProblemPhyXMini0205.maximumDivingBoardAmplitude}`
  and `\leanok`.

## LeanExplore queries and candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`. Queries run:

- `Dimensionful WithDim physical quantity length time acceleration force frequency`
- `simple harmonic motion acceleration equals negative angular frequency squared times displacement`
- `contact normal force nonnegative Newton second law vertical motion`
- `WithDim UnitChoices.SI dimension L𝓭 T𝓭 M𝓭`
- `WithDim`
- `Real.cos Real.pi`

Candidates fetched and used:

- `Dimensionful` (id 394284), module `Physlib.Units.Basic`: its source confirms
  a unit-choice-indexed subtype satisfying dimensional scaling.
- `WithDim` (id 394425), module `Physlib.Units.WithDim.Basic`: its source
  confirms the dimension-tagged carrier used for each physical quantity.
- `UnitChoices.SI` (id 394270), module `Physlib.Units.Basic`: its source
  confirms the meter-second-kilogram SI choices used by the named readouts.

Candidates inspected as near misses:

- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory` and
  `.trajectory_acceleration` (ids 385312 and 385317), from
  `Physlib.ClassicalMechanics.HarmonicOscillator.Solution`, model a
  Euclidean mass-spring trajectory using scalar time and oscillator data.
- `ClassicalMechanics.HarmonicOscillator.ω` (id 385208) is specifically
  `√(k/m)`. The diving board problem instead supplies a frequency directly and
  requires dimensionful board/contact quantities, so these APIs were not used.
- `UnitExamples.NewtonsSecondWithDim` (id 394350) confirms the dimensions of
  `F = ma`, but it operates on single `WithDim` values in one unit choice and
  does not express the amplitude-indexed unilateral-contact law required here.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `Dimension.M𝓭`, and `UnitChoices.SI`.
- Mathlib: `Real.cos`, `Real.pi`, real absolute value, real powers, order, and
  arithmetic used in the SHM laws and numerical-choice conclusions.

## Local abstractions introduced

- The seven physical quantity names are `Dimensionful (WithDim ... ℝ)` types,
  not transparent scalar aliases; their SI projections are separately named
  real-valued readouts.
- `DivingBoardPebbleSetup` preserves the physical roles of the board end,
  pebble, cyclic and angular frequencies, gravity, mass, displacement,
  acceleration, normal force, and turning time.
- `SatisfiesDivingBoardContactLaws` is a local governing-law interface because
  the available oscillator API does not model a prescribed-frequency board
  with unilateral pebble contact.
- Amplitude-indexed motion is used so maximality is a genuine comparison over
  candidate physical amplitudes rather than a premise naming the desired
  answer.

## Grounding gaps and redraft requests

- No matching Mathlib/Physlib API was found for unilateral normal contact on a
  prescribed vertically oscillating support. The local law interface preserves
  the required physics without importing the result to be shown.
- The blueprint chapter contains `% archon:physics` but no informal derivation,
  does not print units on the answer choices, and does not state the gravity
  value. The formalization makes the textbook interpretation explicit:
  choices are meter readouts and `g = 9.8 m/s²`. A plan-agent redraft should
  record those conventions and the derivation `N = m(g - ω²A)` at the upper
  turning point.
- The requested `.archon/AGENTS.md` is absent in this project checkout. The
  available `.archon/prover-modes/physics-formalize.md` supplied the role
  discipline. The assigned Lean file contains no `/- USER: ... -/` hint.
- The advertised `archon dag-query` command was unavailable on `PATH`, so the
  optional dependency query could not run. The source report independently
  confirms that there are no previous-part dependencies.

## Verification

- `archon-lean-lsp` diagnostics succeeded with exactly one expected
  `declaration uses sorry` warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0205.lean` exited with code
  0 and the same single expected warning.
