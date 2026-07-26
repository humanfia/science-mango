# Autoformalization result: `problem_phyx_mini_0281.lean`

## Assumption/target split

### Governing laws

- Static balance of the hanging block: in coherent SI readouts,
  `k * h = m * g`.
- Spring small-oscillation law: the block and spring are represented by
  Physlib's `ClassicalMechanics.HarmonicOscillator`, so their angular
  frequency is its `ω = sqrt (k / m)`.
- Simple-pendulum small-angle law: the angular coordinate is represented by a
  generalized Physlib harmonic oscillator with inertia `m_bob * L^2` and
  gravitational restoring coefficient `m_bob * g * L`.
- Angular-to-cyclic conversion `ω = 2 * π * f` is recorded independently for
  the spring and pendulum.
- The design condition `PendulumMatchesSpringFrequency` equates only the two
  cyclic-frequency readouts. It does not constrain the pendulum length.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- The primary image has three panels: unloaded spring, the same loaded spring,
  and a fixed-pivot simple pendulum.
- Direct inspection of `phyx_data/test_image/281.png` shows an ordinary pivot,
  string, and bob in the pendulum panel.  The auxiliary caption's mention of a
  pulley was therefore not adopted as primary-image evidence.
- The spring is fixed at its upper end; the block appears only in the loaded
  panel; the pendulum panel shows a pivot, string, and bob.
- Label `k` denotes spring stiffness. Label `h` denotes the vertical endpoint
  separation between the unloaded and loaded configurations.
- The prose supplies `h = 2.0 cm`, a positive short downward pull, release from
  rest, and vertical small oscillations about static equilibrium.
- The requested device is a simple point-bob/massless-string pendulum in the
  standard small-angle regime.
- Positivity hypotheses select the nondegenerate physical branch for masses,
  stiffness, extension, gravity, pendulum length, and frequencies.
- The four displayed choices are represented as source metadata: A `1.60 cm`,
  B `1.80 cm`, C `2.20 cm`, and D `2.00 cm`.

### Current target conclusions

- Generic intermediate conclusion:
  `setup.pendulumLength = setup.equilibriumExtension_h`.
- Problem-specific conclusion: the pendulum length has centimetre readout `2`.
- The resulting length matches recorded answer choice `D`.

## Goal-faithfulness audit

The requested equality `L = h`, the numerical readout `L = 2 cm`, and answer
agreement with D occur only on the conclusion side of
`matchingFrequency_pendulumLength_eq_equilibriumExtension` and
`problem_phyx_mini_0281`. They are absent from `SpringPendulumSetup`,
`MatchesProblemDescription`, `HasPhysicalParameters`,
`SatisfiesSpringAndPendulumLaws`, and `PendulumMatchesSpringFrequency`.

`MatchesProblemDescription` assigns `2 cm` only to the measured spring
extension `h`, not to the unknown pendulum length. The frequency-match
predicate equates frequencies only. The pendulum generalized oscillator is a
general law depending on an unconstrained positive `pendulumLength`; it is not
defined from `h`. Thus the target does not follow by unfolding any setup or
law predicate. The answer-choice table is a transcription of all displayed
options; unfolding it still leaves the substantive derived obligation that
the pendulum length is `2 cm`.

## Declarations created and blueprint correspondence

- Dimensionful roles and unit readouts: `MassQuantity`, `LengthQuantity`,
  `VelocityQuantity`, `AccelerationQuantity`, `SpringStiffnessQuantity`,
  `FrequencyQuantity`, `AngularFrequencyQuantity`, and their named readout
  functions.
- Figure model: `FigurePanel`, `FigureLabel`, `FigureQuantityRole`,
  `SpringPendulumFigure`, and `MatchesPrimaryFigure`.
- Physical setup and data: `MotionOrientation`, `OscillationRegime`,
  `PendulumModel`, `SpringPendulumSetup`, `MatchesProblemDescription`, and
  `HasPhysicalParameters`.
- Governing model: `springOscillatorSI`, `pendulumOscillatorSI`,
  `SatisfiesSpringAndPendulumLaws`, and `PendulumMatchesSpringFrequency`.
- Answer metadata: `AnswerChoice`, `AnswerChoice.lengthInCentimeters`,
  `recordedAnswerChoice`, and `MatchesAnswerChoice`.
- Helper lemma:
  `matchingFrequency_pendulumLength_eq_equilibriumExtension`.
- Main theorem `problem_phyx_mini_0281` corresponds to blueprint label
  `thm:physics:phyx_mini_0281:target`.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `mass spring harmonic oscillator angular frequency
  square root spring constant divided by mass` found the applicable
  `ClassicalMechanics.HarmonicOscillator`, its `ω`, and its `ω_sq` theorem.
- Natural-language query `simple pendulum small angle oscillation angular
  frequency square root gravity divided by length` returned the generic
  harmonic oscillator and an unrelated sliding-pendulum configuration space,
  but no ordinary simple-pendulum frequency declaration.
- Natural-language query `Dimensionful WithDim physical quantity SI units
  length mass time` found `UnitChoices.SI`, `Dimensionful`, `Dimension`, and
  `Dimension.L𝓭`.
- Natural/literal query `LengthUnit.centimeters UnitChoices.SI` found the exact
  centimetre unit and SI unit-choice declarations.
- Likely-name queries `ClassicalMechanics.HarmonicOscillator.ω`,
  `Dimensionful`, `WithDim`, and `Dimension.M𝓭 Dimension.T𝓭` confirmed the
  names used by the model.

Source and module details were fetched for the declarations actually used to
shape the model: `ClassicalMechanics.HarmonicOscillator`, its `ω`,
`Dimensionful`, `WithDim`, `UnitChoices.SI`, `Dimension.L𝓭`,
`Dimension.M𝓭`, and `LengthUnit.centimeters`.  In particular, the retrieved
source confirms that Physlib defines `ω` as `Real.sqrt (k / m)` and defines
centimetres as `10⁻²` metres.

## PhysLean/Mathlib names grounded

- `ClassicalMechanics.HarmonicOscillator`
- `ClassicalMechanics.HarmonicOscillator.ω`
- `ClassicalMechanics.HarmonicOscillator.ω_sq` (available to the later prover)
- `Dimensionful`
- `WithDim`
- `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`
- `UnitChoices.SI`
- `LengthUnit.meters`, `LengthUnit.centimeters`
- `Real.pi`

The relevant Physlib modules are
`Physlib.ClassicalMechanics.HarmonicOscillator.Basic`,
`Physlib.Units.Basic`/`Physlib.Units.WithDim.Basic`, and
`Physlib.SpaceAndTime.Space.LengthUnit` (transitively available through the
chosen units import).

## Local abstractions introduced

- Dimensionful aliases name the physical roles and dimensions needed by the
  problem. They are not transparent aliases to `ℝ`; real numbers are exposed
  only by explicitly named coherent-unit readouts.
- `SpringPendulumFigure` preserves the three panels, fixed supports, block,
  string, bob, and the roles of labels `k` and `h`.
- `SpringPendulumSetup` keeps the block mass, bob mass, stiffness, extension,
  gravity, release data, both physical frequencies, and the unknown pendulum
  length independent.
- `pendulumOscillatorSI` is the smallest faithful replacement for a missing
  dedicated simple-pendulum API: it represents the general small-angle angular
  equation through generalized inertia and restoring coefficient, retaining
  bob mass even though it later cancels.
- `SatisfiesSpringAndPendulumLaws` records only general mechanics laws.

## Grounding gaps

- LeanExplore returned no dedicated simple-pendulum small-angle frequency
  declaration in the searched Mathlib/Physlib corpus. The generalized
  `ClassicalMechanics.HarmonicOscillator` construction is used instead.
- No dedicated API was found for static equilibrium of a vertically hanging
  spring, so `k h = m g` is stated explicitly as a governing-law field.

## Verification and redraft notes

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0281.lean` succeeds with
  only the two expected `declaration uses sorry` warnings.
- `archon-lean-lsp` diagnostics independently report the same two warnings at
  the helper lemma and main theorem and no errors or failed dependencies.
- The iteration-001 gate reason was missing post-formalization evidence.  This
  file is the requested post-formalization report and records the searches,
  candidates, primary-image audit, grounded names, local abstractions, gaps,
  and assumption/target split actually checked against the compiling model.
- The requested `.archon/AGENTS.md` was absent in this checkout; the complete
  `.archon/prover-modes/physics-formalize.md` role document was used instead.
- The assigned Lean file contains no `/- USER: ... -/` comments, so there were
  no additional file-specific hints to apply.
- The `archon` executable was not available on `PATH`, so no DAG query result
  was available; the source report records no previous parts.
- The existing blueprint chapter was not edited because the task's explicit
  write permissions allow changes only to the assigned Lean file and this
  result file. A coordinator with blueprint write permission should add
  `\leanok` to `thm:physics:phyx_mini_0281:target` after accepting this
  formalization.
