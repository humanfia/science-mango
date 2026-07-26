# Autoformalization result: `problem_phyx_mini_0170.lean`

Iteration 002 revalidated the complete existing formalization against the
review-gate reason, the source report, and the primary image.  The gate's only
reported failure was the absence of post-formalization evidence; the audited
Lean model required no semantic redraft.

## Assumption/target split

### Governing laws

- `HasCommonSinusoidalInPhaseDrive` states that speakers `A` and `B` use the
  same depicted amplifier, emit sinusoidal waves, and have equal source phase
  at every positive test frequency.
- `HasPhysicalAcousticParameters` supplies positivity of propagation speed and
  wavelength, and nonnegativity of the two direct path lengths.
- `SatisfiesTwoSourceAcousticLaws.wave_speed_relation` is the uniform acoustic
  dispersion relation `c = lambda * f` in named SI readouts.
- `SatisfiesTwoSourceAcousticLaws.destructive_interference_iff` is the general
  in-phase-source law
  `pathDifference = (order + 1/2) * wavelength`, quantified over every positive
  frequency and every natural interference order. It does not select order
  zero or any numerical frequency.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- `MatchesDepictedLineGeometry` preserves the primary-image labels
  `A`, `P`, `B`, `Q`, the ordering `A < P < B < Q`, `AB = 2 m`, `BQ = 1 m`,
  the label `AP = x`, and two direct source-to-`Q` paths.
- The primary image, rather than its inaccurate auxiliary caption, was used
  for the segment labels: it clearly marks the `2.00 m` span from `A` to `B`
  and the `1.00 m` span from `B` to `Q`.
- `UsesStandardAirSoundSpeed` makes the conventional `344 m/s` sound-speed
  calibration explicit. This readout is needed to turn the symbolic result
  `f_min = c / 4 m` into the recorded `86 Hz`; it is not printed in the source
  problem and is therefore also recorded below as a grounding gap.
- `AnswerChoice.frequencyHertz` records the four supplied answer-table values,
  and `recordedDatasetAnswer` records metadata answer A. Neither is a theorem
  premise.

### Current target conclusions

- `pathDifferenceAtQ_eq_two_meters` concludes the derived direct-path
  difference `|AQ - BQ| = 2 m`.
- `problem_phyx_mini_0170` concludes that the physical frequency constructed
  from the `86 Hz` readout is the least positive frequency producing
  destructive interference at `Q`, and that it agrees with recorded answer A.
  This corresponds to blueprint label
  `thm:physics:phyx_mini_0170:target`.

## Goal-faithfulness audit

The requested `86 Hz` result is absent from every hypothesis structure and
governing-law field. `TwoLoudspeakerInterferenceSetup.destructiveInterferenceAtQ`
is an uninterpreted physical observable; it is not defined by the answer table
or by the target equality. The acoustic law relates that observable uniformly
to all positive frequencies and all natural orders, so it does not assume
that `86 Hz` is destructive or least.

The only added numerical calibration is the physically distinct propagation
speed `344 m/s`. Together with the independently depicted `2 m` path
difference, the general order-zero half-wavelength law yields wavelength
`4 m` and hence `344 / 4 = 86 Hz`. Thus this calibration does not restate the
current target. `frequencyInHertz` is a generic unit-aware constructor for any
real readout; specializing it to `86` occurs only in the theorem conclusion
and does not make either destructiveness or minimality true by unfolding.

The auxiliary point `P` and distance `x` remain in the model even though they
drop out of the final calculation. Speaker identities, the common amplifier,
waveform type, phases, direct paths, and physical dimensions are likewise
preserved rather than collapsed to unrelated scalar aliases.

## Declarations created

- Dimensionful quantities and readouts:
  `AcousticLength`, `AcousticFrequency`, `AcousticSpeed`, `metersValue`,
  `hertzValue`, `metersPerSecondValue`, and generic `frequencyInHertz`.
- Physical/figure labels:
  `FigurePoint`, `SpeakerLabel`, `AmplifierLabel`, `WaveformKind`,
  `PropagationKind`, and `AcousticPath`.
- Setup and premises:
  `TwoLoudspeakerInterferenceSetup`, `HasCommonSinusoidalInPhaseDrive`,
  `MatchesDepictedLineGeometry`, `HasPhysicalAcousticParameters`,
  `UsesStandardAirSoundSpeed`, and `SatisfiesTwoSourceAcousticLaws`.
- Derived predicates and metadata:
  `pathDifferenceAtQInMeters`, `IsPositiveFrequency`,
  `IsLowestDestructiveFrequency`, `AnswerChoice`,
  `MatchesDisplayedFrequency`, and `recordedDatasetAnswer`.
- By-sorry declarations:
  `pathDifferenceAtQ_eq_two_meters` and `problem_phyx_mini_0170`.
- Blueprint correspondence:
  `problem_phyx_mini_0170` formalizes
  `thm:physics:phyx_mini_0170:target`; the geometric lemma is an explicit
  intermediate extracted from the same chapter and primary figure.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`.

- Iteration 002 reran the exact queries
  `unit-independent dimensionful SI physical quantity length frequency speed`,
  `WithDim Dimension.L𝓭 Dimension.T𝓭 physical dimension`, `Dimension.T𝓭`,
  `phase angle modulo full turn Real.Angle`, and
  `destructive interference path difference odd half wavelength two in-phase sound sources`.
  The dimensional and angle searches returned the declarations used below;
  the interference search returned
  `ClassicalMechanics.transverseHarmonicPlaneWave` plus unrelated parity,
  harmonic-function, and topological-path declarations, but no compatible
  two-source acoustic interference law.

- `SI physical quantity length frequency speed`, `PhysicalQuantity`,
  `Dimension.Time`, `frequency dimension inverse time`,
  `speed dimension length divided by time`, and
  `SI meter hertz physical quantity` found the Physlib dimensional API.
  Used candidates include `Dimensionful` (ID 394284), `Dimension` (394292),
  `Dimension.L𝓭` (394324), `Dimension.T𝓭` (394330),
  `UnitChoices.SI` (394270), `WithDim` (394425), and
  `CarriesDimension.toDimensionful` (394290).
- Source/module information was fetched for the used declarations above.
  The relevant modules are `Physlib.Units.Basic`,
  `Physlib.Units.Dimension`, and `Physlib.Units.WithDim.Basic`.
- `Real.Angle phase modulo full turn` found and grounded `Real.Angle`
  (ID 146415) in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`; it is used for
  source phase rather than an untyped scalar phase.
- `sound wave wavelength frequency relation` returned Physlib candidates such
  as `ClassicalMechanics.harmonicWave`, `planeWave`, and `WaveEquation`.
  They model general field-valued plane waves but do not supply this problem's
  acoustic two-source path-difference observable, so they were not forced into
  the model.
- `destructive interference path difference half wavelength` returned only
  unrelated topological `Path` declarations and `sub_half`; no matching
  acoustic interference API was found.
- `sinusoidal waves phase in phase` returned harmonic-oscillator/plane-wave
  candidates and `Real.Angle` was separately selected for the phase role.
- `absolute value real abs` returned bundled/rational absolute-value
  declarations that were unnecessary; standard real `|x|` notation was
  verified by Lean elaboration instead.
- Additional inspected near-misses/examples were `UnitExamples.SpeedEq`,
  `UnitExamples.meters400`, `DimSpeed`, and
  `DimSpeed.oneMeterPerSecond`. They helped confirm the intended dimension
  expressions but were not needed as declarations in this file.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `UnitChoices.SI`, and `CarriesDimension.toDimensionful`.
- Mathlib: `Real.Angle`, `ℝ`, `ℕ`, order/equality connectives, and real
  absolute-value notation.

## Local abstractions introduced

- `TwoLoudspeakerInterferenceSetup` retains the two speaker identities,
  amplifier connection, waveform, phase, sound speed, wavelength family,
  collinear positions, propagation paths, and destructive-interference
  observable.
- `AcousticPath` distinguishes direct propagation from reflection and retains
  physical source, destination, and dimensionful length.
- `SatisfiesTwoSourceAcousticLaws` is the smallest local governing-law
  interface needed because the library search exposed no acoustic
  odd-half-wavelength interference declaration.
- `IsLowestDestructiveFrequency` expresses positivity, actual destructive
  interference, and comparison with every other positive destructive
  frequency. It does not define the least frequency as a fixed scalar.

These abstractions preserve physical roles while all dimensional primitives
remain Physlib quantities; only named SI readouts, answer values, coordinates,
and dimensionless orders use real scalars.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration was found for two-source acoustic destructive
  interference or its odd-half-wavelength path-difference rule. The local law
  interface should remain unless such an API is added later.
- The problem text and figure do not state the sound speed. The numerical
  answer `86 Hz` requires a convention; this formalization explicitly uses
  `344 m/s`, which makes the recorded result exact. The plan/blueprint should
  state this calibration (or state a rounding convention with a different
  standard speed) so the numerical target is fully source-grounded.
- The auxiliary caption describes the `2.00 m` and `1.00 m` segmentation
  incorrectly. The scenario text and primary image agree on `AB = 2.00 m` and
  `BQ = 1.00 m`; those were treated as authoritative.
- `.archon/AGENTS.md` was absent in this project checkout. The available
  `.archon/prover-modes/physics-formalize.md` and the task instructions were
  followed instead.
- The blueprint chapter was not edited to add `\leanok`, because the task's
  explicit write permissions restrict edits to the assigned Lean file and
  this result file. A plan/blueprint owner should add the marker.
- The chapter contains the required `% archon:physics` marker, but its theorem
  environment only gives the autoformalization directive rather than the
  promised informal derivation. A plan-agent redraft should record
  `AQ = 3 m`, `BQ = 1 m`, `Delta r = 2 m`, the order-zero destructive
  wavelength `lambda = 4 m`, and the explicit `344 m/s` calibration yielding
  `f = 86 Hz`.
- The assigned Lean file contains no `/- USER: ... -/` comments, so there were
  no file-specific hints to apply.

## Verification

- `archon-lean-lsp` diagnostics: success, with only the two expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0170.lean`: exit code 0,
  with the same two expected warnings.
- The requested `archon dag-query` navigation command was unavailable because
  `archon` was not on `PATH` in this runtime.
