# Autoformalization result: `problem_phyx_mini_0196.lean`

## Assumption/target split

### Governing laws

- `SatisfiesLeftwardAcousticDopplerLaw.frequencyLaw` states the general
  one-dimensional acoustic Doppler relation for a wave travelling from source
  `S` to listener `L`, opposite the positive road axis. The source and listener
  velocities are relative to the still air. The relation contains no numerical
  answer choice.
- `HasSubsonicPhysicalParameters` records positive emitted frequency and sound
  speed plus subsonic bounds for both moving participants. It selects the
  ordinary physical branch and contains no requested heard-frequency value.

### Previous-part results / shared calibration

- `UsesPriorSirenCalibration` records the shared calibration from source panel
  193 of the same police-siren sequence: a sinusoidal `300 Hz` emission and
  sound speed `340 m/s` in still air.
- This calibration is intentionally separate from `MatchesPrimaryFigure`:
  neither number is printed in image `196.png`, and without carried exercise
  context the current panel alone does not determine a numerical frequency.

### Figure/data readouts

- `MatchesPrimaryFigure` records the primary image's geometry and labels: `L`
  is left of `S`; the positive direction is `L` to `S`; sound reaching `L`
  propagates from `S` to `L`; and the air-relative axial velocity readouts are
  `v_L = 15 m/s` and `v_S = 45 m/s`.
- `AnswerChoice.hertz` records the displayed table `A = 267`, `B = 277`,
  `C = 274`, and `D = 268` hertz.
- `recordedDatasetAnswer` records the dataset metadata label `B`.

### Current target conclusions

- `heardFrequency_hertz_eq_calibratedRatio` derives the exact unrounded
  readout `300 * (340 + 15) / (340 + 45)`.
- `heardFrequency_matches_recordedChoiceB` concludes that the dimensionful
  heard frequency lies within half a hertz of choice B's `277 Hz`, matching
  nearest-whole-hertz presentation rather than asserting a false exact integer
  equality.

## Goal-faithfulness audit

- `SirenListenerDopplerSetup.heardFrequency` is an unknown dimensionful
  observable. No setup field gives it `277 Hz`, an answer label, or the
  calibrated ratio.
- `MatchesPrimaryFigure`, `UsesPriorSirenCalibration`, and
  `HasSubsonicPhysicalParameters` do not mention the heard-frequency answer.
- The Doppler premise states a general source/observer law. The exact ratio is
  obtained only after substituting independent figure and calibration data in
  the supporting lemma.
- `MatchesAnswerChoice` is generic in both physical frequency and choice, and
  `recordedDatasetAnswer` only names metadata. Unfolding either definition does
  not prove that the observable matches B.
- The target remains a substantive conclusion with a `sorry` body as required
  by `physics-formalize`; it is not true by reflexivity or definitional
  unfolding.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0196:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0196.heardFrequency_matches_recordedChoiceB`.
- Supporting derived lemma:
  `PhyXMiniProblems.ProblemPhyXMini0196.heardFrequency_hertz_eq_calibratedRatio`.
  The current blueprint has no separate label for this public lemma.
- Dimensionful model and readouts: `AcousticFrequency`, `AxialPosition`,
  `AxialVelocity`, `frequencyReadout`, `frequencyInHertz`, `positionReadout`,
  `positionInMeters`, `axialVelocityReadout`,
  `axialVelocityInMetersPerSecond`, and `speedInMetersPerSecond`.
- Physical labels and setup: `Participant`, `RoadDirection`, `WaveformKind`,
  and `SirenListenerDopplerSetup`.
- Assumption interfaces: `MatchesPrimaryFigure`, `UsesPriorSirenCalibration`,
  `HasSubsonicPhysicalParameters`, and
  `SatisfiesLeftwardAcousticDopplerLaw`.
- Answer metadata and matching relation: `AnswerChoice`,
  `AnswerChoice.hertz`, `recordedDatasetAnswer`, and `MatchesAnswerChoice`.
  These supporting declarations have no individual blueprint labels in the
  protected chapter.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- `Doppler effect sound frequency moving source observer` returned
  `ClassicalMechanics.planeWave` and `ClassicalMechanics.WaveEquation` as
  conceptual near matches, but no law for independently moving acoustic source
  and observer.
- `Dimensionful WithDim inverse time acoustic frequency` returned
  `Dimensionful` and `UnitExamples.CosDim`; the latter confirms Physlib's
  inverse-time dimension spelling `T𝓭⁻¹`.
- `DimSpeed physical velocity meters per second SI units` returned `DimSpeed`,
  `DimSpeed.oneMeterPerSecond`, and `UnitChoices.SI`.
- `TimeUnit.seconds LengthUnit.meters UnitChoices.SI` grounded the SI unit
  selection; the fetched source of `UnitChoices.SI` explicitly assigns
  `LengthUnit.meters` and `TimeUnit.seconds`.
- Likely-name searches `WithDim`, `TimeUnit.seconds`, and `LengthUnit.meters`
  found the exact first two declarations. `LengthUnit.meters` did not appear in
  its short result list, but it is explicitly present in the fetched
  `UnitChoices.SI` source.

Source, module, and docstring were fetched only for candidates used to ground
the model: `Dimensionful` (`Physlib.Units.Basic`), `WithDim`
(`Physlib.Units.WithDim.Basic`), `DimSpeed`
(`Physlib.Units.WithDim.Speed`), `UnitChoices.SI`
(`Physlib.Units.Basic`), `TimeUnit.seconds`
(`Physlib.SpaceAndTime.Time.TimeUnit`), and `UnitExamples.CosDim`
(`Physlib.Units.Examples`).

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `DimSpeed`, `UnitChoices.SI`, `LengthUnit.meters`, and `TimeUnit.seconds`.
- Mathlib: `ℝ`, `NNReal`, real absolute value notation, and ordered-field
  arithmetic used by the readouts and tolerance predicate.
- The file now explicitly imports both `Mathlib` and
  `Physlib.Units.WithDim.Speed`. This directly addresses the iteration-001 gate
  reason that the target did not explicitly import Mathlib.

## Local abstractions introduced

- `AcousticFrequency := Dimensionful (WithDim T𝓭⁻¹ NNReal)` retains the
  inverse-time dimension and nonnegative physical magnitude because no
  dedicated acoustic-frequency type was found.
- `AxialPosition := Dimensionful (WithDim L𝓭 ℝ)` retains length dimension and
  permits signed coordinates along the depicted road.
- `AxialVelocity := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)` retains velocity
  dimension and permits signed direction. Physlib's `DimSpeed` uses `NNReal`,
  so it remains appropriate for sound-speed magnitude but not signed road
  velocity.
- `SatisfiesLeftwardAcousticDopplerLaw` is the smallest local governing-law
  interface needed because the search found no matching acoustic Doppler API.
  Its formula is independent of every displayed answer.
- The participant, direction, waveform, setup, and answer-choice types retain
  the image's semantic labels instead of collapsing physical objects to raw
  scalars.

## Grounding gaps

- Mathlib/Physlib exposes wave-equation and plane-wave objects but no located
  one-dimensional acoustic Doppler law for independently moving source and
  listener; the faithful local law interface fills this gap.
- The current image and chapter omit emitted frequency and sound speed. Their
  values were verified in source panel 193 of the same police-siren sequence
  and are modeled explicitly as carried calibration, not as current-image
  readouts.
- The requested `.archon/AGENTS.md` does not exist in this checkout. The
  available role document `.archon/prover-modes/physics-formalize.md` was read
  in full and followed instead.
- The `archon` executable is not available on `PATH`, so the optional DAG node
  and ancestor queries could not be run. The target chapter declares no
  explicit dependency labels.

## Verification and blueprint redraft requests

- `archon-lean-lsp` reports only the two expected `declaration uses sorry`
  warnings, at the supporting lemma and target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0196.lean` exits with code
  0 and the same two expected warnings.
- Blueprint edits are forbidden by this task's final write-permission rule.
  An authorized blueprint agent should attach
  `\lean{PhyXMiniProblems.ProblemPhyXMini0196.heardFrequency_matches_recordedChoiceB}`
  and `\leanok` to `thm:physics:phyx_mini_0196:target`.
- Because the public supporting lemma has no blueprint environment, an
  authorized planner should either add an environment for
  `heardFrequency_hertz_eq_calibratedRatio` or explicitly classify it as
  statement-support infrastructure.
