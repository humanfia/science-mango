# Prover result: `problem_phyx_mini_0222.lean`

## Archon iteration 015

All three placeholders were replaced by faithful proofs without changing any
declaration signature:

- `heardFrequenciesInHertz_eq_exactModelValues` substitutes the figure,
  standard-air, and directional Doppler-law fields and proves the two exact
  rational received frequencies by normalized real arithmetic.
- `beatFrequencyInHertz_eq_exactModelValue` applies the beat-frequency law,
  rewrites with the received-frequency lemma, and evaluates the resulting
  absolute rational difference.
- `beatFrequencyAtB_matches_recordedAnswerD` reuses the exact beat-frequency
  lemma and proves that its distance from the displayed `24 Hz` value is at
  most `1/2 Hz`.

### Verification

- Archon Lean LSP diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0222.lean`: exit code 0.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom verification for
  `PhyXMiniProblems.ProblemPhyXMini0222.beatFrequencyAtB_matches_recordedAnswerD`
  reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

### Remaining coordination note

The corresponding blueprint environments should be marked `\leanok`. This
prover task's explicit write permissions allow changes only to the assigned
Lean file and this result file, so the blueprint chapter was not edited.

No redraft is needed.

---

# Earlier autoformalization retry result: `problem_phyx_mini_0222.lean`

Archon iteration 002. The review-gate reason was: “physics target does not import
Mathlib; autoformalization must be checked in a real Lake/Mathlib environment,
not as a standalone Lean smoke file.” The target now explicitly imports both
`Mathlib` and `Physlib.Units.WithDim.Speed`, and it has been rechecked in the
project's Lake environment.

## Assumption/target split

### Governing laws

- `HasPhysicalDopplerParameters` records positivity of emitted/heard
  frequencies and sound speed, plus subsonic source motion relative to the air.
- `SatisfiesDirectionalMovingSourceDopplerLaws` states the classical
  one-dimensional acoustic Doppler relation separately for the rightward ray
  from the rear source and the leftward ray from the front source. The laws are
  symbolic in emitted frequency, received frequency, sound speed, observer
  velocity, source velocity, and air velocity.
- `SatisfiesBeatFrequencyLaw` states that the beat-frequency SI readout is the
  magnitude of the difference between the two received-frequency readouts.

### Previous-part results

- None. The source report has an empty `previous_parts` list. The documented
  `archon dag-query` could not be run because `archon` is not available on this
  runtime's `PATH`.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records the shared railroad-car carrier,
  rear/left and front/right speaker assignments, the image order
  `C < rear speaker < B < front speaker < A`, stationary observer `B`, car and
  source velocity `12 m/s` rightward, identical emissions with a `348 Hz`
  readout, and the two propagation directions toward `B`.
- The primary bitmap `phyx_data/test_image/222.png` was inspected directly. It
  places `B` on the stationary ground between the loudspeakers. This agrees
  with the problem's “stationary observer” wording and overrides the auxiliary
  caption's incompatible claim that `B` stands on the moving platform.
- `UsesStandardStillAir` separately supplies still air and a conventional
  `343 m/s` sound speed. Neither value is misrepresented as a figure readout.
- `AnswerChoice.hertz` and `recordedAnswerChoice` reproduce the four displayed
  answers and dataset answer label D.

### Current target conclusions

- `heardFrequenciesInHertz_eq_exactModelValues` derives the intermediate
  readouts `119364 / 331 Hz` and `119364 / 355 Hz`.
- `beatFrequencyInHertz_eq_exactModelValue` concludes the exact model value
  `2864736 / 117505 Hz`, approximately `24.38 Hz`.
- `beatFrequencyAtB_matches_recordedAnswerD` concludes both that exact physical
  readout and its half-hertz-tolerance match with displayed answer D (`24 Hz`).

## Goal-faithfulness audit

- `heardFrequencyAtB` and `beatFrequencyAtB` are independent fields of the
  dimensionful physical setup. No setup definition assigns them a formula or a
  numerical value.
- No hypothesis or premise field contains `2864736 / 117505`, the numerical
  answer `24 Hz`, answer D, or an equivalent beat-frequency conclusion.
- The Doppler premises are genuine governing relations and do not mention a
  target answer. The beat premise only relates the three independent physical
  frequencies and does not determine either received frequency by itself.
- The numerical premises are source data (`348 Hz`, `12 m/s`) and the explicitly
  separated ambient calibration (`343 m/s`, still air).
- The answer-table definitions encode supplied metadata only. Unfolding them
  cannot establish the exact Doppler value or the rounding inequality.
- The final theorem is a relation about the physical beat-frequency quantity,
  not `True`, reflexive equality, or an unrelated scalar tautology.

## Declarations and blueprint correspondence

- Dimensioned quantities/readouts: `AcousticFrequency`, `AxialPosition`,
  `AxialVelocity`, `frequencyInHertz`, `positionInMeters`,
  `axialVelocityInMetersPerSecond`, and `speedInMetersPerSecond`.
- Figure/physical labels: `FigurePerson`, `SpeakerLabel`, `RailroadCarEnd`,
  `VehicleLabel`, and `AxialDirection`.
- Setup and relative-velocity helpers: `MovingRailroadCarSpeakerSetup`,
  `speakerVelocityRelativeToAirInMetersPerSecond`, and
  `observerBVelocityRelativeToAirInMetersPerSecond`.
- Premise interfaces: `MatchesProblemAndPrimaryFigure`, `UsesStandardStillAir`,
  `HasPhysicalDopplerParameters`,
  `SatisfiesDirectionalMovingSourceDopplerLaws`, and
  `SatisfiesBeatFrequencyLaw`.
- Derived statements: `heardFrequenciesInHertz_eq_exactModelValues` and
  `beatFrequencyInHertz_eq_exactModelValue`.
- Answer representation: `AnswerChoice`, `AnswerChoice.hertz`,
  `recordedAnswerChoice`, and `MatchesAnswerChoice`.
- `beatFrequencyAtB_matches_recordedAnswerD` corresponds to blueprint label
  `thm:physics:phyx_mini_0222:target`. The preceding public declarations are
  unavoidable model support declarations and currently have no separate
  blueprint labels.

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- `classical acoustic Doppler effect moving sound source stationary observer
  beat frequency`: no matching acoustic Doppler or beat-frequency declaration;
  returned candidates concerned harmonic oscillators and stationary sets.
- `Doppler`: the only physics-adjacent candidate was
  `ClassicalMechanics.planeWave`, which is not a moving-source acoustic Doppler
  law and was therefore not used.
- `dimensionful physical quantity SI unit choice speed`: selected
  `Dimensionful` (id 394284), `UnitChoices.SI` (id 394270), and `DimSpeed`
  (id 394481).
- `WithDim inverse time frequency`: selected `WithDim` (id 394425); no
  ready-made ordinary/acoustic frequency type was returned.
- Source, module, and docstring were fetched for each selected candidate only.
  They locate `Dimensionful` and `UnitChoices.SI` in `Physlib.Units.Basic`,
  `DimSpeed` in `Physlib.Units.WithDim.Speed`, and `WithDim` in
  `Physlib.Units.WithDim.Basic`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `UnitChoices.SI`, and `DimSpeed`.
- Mathlib/Core through the explicit `Mathlib` import: `NNReal`, `ℝ`, real
  absolute-value notation, order relations, and real division.
- Lean LSP elaboration additionally confirmed the two imports, the dimensioned
  readout types, and the final theorem signature.

## Local abstractions introduced

- `AcousticFrequency` is `Dimensionful (WithDim T𝓭⁻¹ NNReal)`, not a scalar
  alias. `AxialPosition` and `AxialVelocity` likewise retain length and signed
  length-per-time dimensions.
- Finite label types preserve the people, speaker roles, car ends, carrier, and
  propagation directions visible in the figure.
- `MovingRailroadCarSpeakerSetup` keeps emitted, received, and beat frequencies
  distinct while preserving source, observer, medium, geometry, and carrier
  roles.
- Local Doppler and beat-law interfaces are required because LeanExplore found
  no suitable Mathlib/Physlib acoustic Doppler or beat-frequency declaration.
  They preserve the governing physics without encoding the requested answer.

## Grounding gaps and redraft requests

- Mathlib/Physlib exposes no matching acoustic moving-source Doppler or beat
  API in the search results; the faithful local law interfaces should remain.
- The source omits air motion and sound speed. The theorem openly conditions
  the exact value on standard still air at `343 m/s`; upstream material should
  confirm this calibration if another convention is intended.
- The auxiliary caption should be corrected upstream because it contradicts
  both the bitmap and the stationary-observer wording.
- `.archon/AGENTS.md` is absent. The available
  `.archon/prover-modes/physics-formalize.md` and the task prompt supplied the
  applicable role instructions.
- The blueprint theorem was not marked `\leanok` because this task's explicit
  write permissions prohibit editing blueprint chapters. The coordinating
  process should add that marker.

## Verification

- Archon Lean LSP diagnostics: exactly three expected `declaration uses sorry`
  warnings, at the two derived lemmas and the final theorem; no errors or
  failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0222.lean`: exit code 0 with
  the same three expected warnings.
