# Autoformalization result: `problem_phyx_mini_0186.lean`

## Iteration 003 review-gate disposition

The exact retry reason was missing post-formalization evidence: the earlier
physics-grounding preflight predated the Lean model and therefore could not
document the APIs and abstractions actually used.  This report was regenerated
after inspecting the completed Lean declarations, source report, blueprint, and
primary image, and after rerunning LeanExplore against both Mathlib and Physlib.
The gate did not identify a semantic defect in the declaration signatures.
The source/image audit likewise found no such defect, so iteration 003 preserves
the existing physical declarations rather than changing their signatures.

The requested `.archon/AGENTS.md` is absent in this checkout.  The injected
role instructions and the complete available
`.archon/prover-modes/physics-formalize.md` were followed instead.  The assigned
Lean file contains no `/- USER: ... -/` hint.

## Assumption/target split

### Governing laws

- `SatisfiesSoundWaveLaw.speed_eq_wavelength_mul_frequency` states the acoustic law `c = λ f` using SI readouts of dimensionful quantities.
- `ProducesMaximumAmplitudeAtListener` states the standard constructive-interference criterion: for coherent equal-amplitude monochromatic sources, every pairwise path difference is an integer multiple of the wavelength.
- `pathLengthMetersAfterMove` uses the metric distance on Physlib's `Space 2`; only speaker 2 is moved, and its leftward shift is modeled by subtracting the displacement from its horizontal coordinate.
- `EmitsCoherentlyWithCommonAmplitude` records equal initial emission phase and the common individual amplitude `a` stated by the problem.
- `HasPhysicalParameters` records positivity of the geometric and acoustic quantities.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `MatchesProblemReadouts`: adjacent spacing `3 m`, listener distance `4 m`, common tone `170 Hz`, sound speed `340 m/s`.
- `HasDepictedLayout`: speaker labels 1/2/3 occur at metre-coordinate readouts `(0,3)`, `(0,0)`, `(0,-3)`, and the listener at `(4,0)`, expressed parametrically through the dimensionful spacing and listener distance.
- `SpeakerLabel` preserves the top-to-bottom numbering in the primary image.
- `AnswerChoice.meters` preserves all four displayed choices: A `0.50 m`, B `2.00 m`, C `0.25 m`, D `1.00 m`.

### Current target conclusions

- `problem_phyx_mini_0186` concludes that the physical length `lengthOfMeters 1` is the least positive leftward displacement producing maximum amplitude.
- The same theorem concludes that the dataset's recorded choice D is correct through `IsCorrectAnswer setup recordedAnswerChoice`.
- Supporting conclusions derive `λ = 2 m`, the original `5,4,5 m` path lengths, and equality of all three path lengths after a `1 m` move.

## Source/law/answer audit

- **Source and image:** the source report gives `170 Hz`, `340 m/s`, a listener
  `4.0 m` in front of speaker 2, equal named arrival amplitude `a`, and answer
  choices A–D.  Direct inspection of `phyx_data/test_image/186.png` confirms
  the top-to-bottom labels 1, 2, 3 and the two adjacent `3.0 m` separations.
- **Laws:** `SatisfiesSoundWaveLaw` records `c = λ f`; the generic
  `ProducesMaximumAmplitudeAtListener` predicate records the coherent-source
  constructive-interference condition as integral-wavelength pairwise path
  differences.  Neither law names the requested displacement.
- **Answer check:** the data imply `λ = 340/170 = 2 m`; the depicted geometry
  gives outer paths `5 m` and an initial middle path `4 m`.  A `1 m` leftward
  move makes the middle path `5 m`, so all phases align.  Positive later
  alignments occur two metres farther at a time, and the least-positive
  condition selects `1 m`, matching recorded choice D.

## Goal-faithfulness audit

No premise contains the requested `1 m` displacement, answer D, or the claim that a particular move produces a maximum. The setup structure stores physical quantities and source/observer data only. `MatchesProblemReadouts`, `HasDepictedLayout`, `EmitsCoherentlyWithCommonAmplitude`, `HasPhysicalParameters`, and `SatisfiesSoundWaveLaw` contain only source data, positivity, source coherence/equal amplitude, geometry, and the generic wave law.

`ProducesMaximumAmplitudeAtListener` is a generic predicate over an arbitrary proposed displacement. `IsLeastPositiveMaximumDisplacement` adds the textbook "first maximum" criterion over all positive displacements, preventing later solutions separated by whole wavelengths from masquerading as the requested answer. Unfolding these definitions does not prove the target: the later prover must derive the 2 m wavelength, calculate Euclidean distances, establish constructive interference at 1 m, and prove minimality.

## Declarations and blueprint labels

All Lean names below have the namespace
`PhyXMiniProblems.ProblemPhyXMini0186` omitted:

| Lean declaration | Blueprint label |
| --- | --- |
| `problem_phyx_mini_0186` | `thm:physics:phyx_mini_0186:target` |
| `AcousticLength` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-acousticlength` |
| `AcousticFrequency` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-acousticfrequency` |
| `AcousticSpeed` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-acousticspeed` |
| `metersValue` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-metersvalue` |
| `hertzValue` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-hertzvalue` |
| `metersPerSecondValue` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-meterspersecondvalue` |
| `lengthOfMeters` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-lengthofmeters` |
| `SpeakerLabel` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-speakerlabel` |
| `ThreeSpeakerInterferenceSetup` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-threespeakerinterferencesetup` |
| `MatchesProblemReadouts` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-matchesproblemreadouts` |
| `HasDepictedLayout` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-hasdepictedlayout` |
| `EmitsCoherentlyWithCommonAmplitude` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-emitscoherentlywithcommonamplitude` |
| `HasPhysicalParameters` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-hasphysicalparameters` |
| `SatisfiesSoundWaveLaw` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-satisfiessoundwavelaw` |
| `movedMiddleSpeakerPosition` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-movedmiddlespeakerposition` |
| `sourcePositionAfterMove` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-sourcepositionaftermove` |
| `pathLengthMetersAfterMove` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-pathlengthmetersaftermove` |
| `ProducesMaximumAmplitudeAtListener` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-producesmaximumamplitudeatlistener` |
| `IsLeastPositiveMaximumDisplacement` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-isleastpositivemaximumdisplacement` |
| `wavelength_in_meters_eq_two` | `lem:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-wavelength-in-meters-eq-two` |
| `initial_path_lengths_are_five_four_five` | `lem:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-initial-path-lengths-are-five-four-five` |
| `one_meter_move_equalizes_path_lengths` | `lem:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-one-meter-move-equalizes-path-lengths` |
| `AnswerChoice` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-answerchoice` |
| `AnswerChoice.meters` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-answerchoice-meters` |
| `IsCorrectAnswer` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-iscorrectanswer` |
| `recordedAnswerChoice` | `def:physics:phyx-mini-0186:phyxminiproblems-problemphyxmini0186-recordedanswerchoice` |

The blueprint theorem environment was not edited with `\leanok` because the task's explicit write permissions allow edits only to the assigned Lean file and this task-result file, and explicitly prohibit editing blueprint chapters.

## LeanExplore queries and candidates

The following queries were actually run in iteration 003 with
`packages: ["Mathlib", "Physlib"]`:

- Natural-language `dimensionful physical quantities SI units length frequency speed`
  returned the used candidates `UnitChoices.SI`, `Dimensionful`, and
  `CarriesDimension.toDimensionful`.
- Natural-language `Euclidean distance between points in Physlib Space n`
  returned the used `Space.dist_eq` and `Space.instDist` candidates, as well as
  Mathlib's `EuclideanSpace` alternatives.
- Natural-language `constructive interference coherent waves path difference integer multiple wavelength`
  returned only unrelated algebraic-localization and topological-path results;
  no acoustic interference API was found.
- Natural-language `wave speed equals wavelength times frequency acoustics`
  returned `ClassicalMechanics.WaveEquation`, `planeWave`, and `harmonicWave`,
  but no scalar acoustic theorem with the signature needed here.
- Likely-name queries `CarriesDimension.toDimensionful`, `WithDim`,
  `Space.dist_eq`, `Real.Angle`, `Dimension.L𝓭`, and `Dimension.T𝓭` grounded
  the exact declarations used in the file.

Source text, module, and docstring were fetched for the candidates actually
used: `UnitChoices.SI`, `Dimensionful`,
`CarriesDimension.toDimensionful`, `WithDim`, `Dimension.L𝓭`,
`Dimension.T𝓭`, `Space.instDist`, `Space.dist_eq`, and `Real.Angle`.  The
fetched module data place the units declarations in `Physlib.Units.Basic`,
`Physlib.Units.WithDim.Basic`, and `Physlib.Units.Dimension`, the metric in
`Physlib.SpaceAndTime.Space.Basic`, and the phase type in
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.

## Physlib/Mathlib names grounded

- Physlib units: `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `UnitChoices.SI`, and
  `CarriesDimension.toDimensionful`.
- Physlib geometry: `Space 2`, its distance instance, and `Space.dist_eq`, whose
  fetched source is the coordinate Euclidean-distance formula used to ground
  `pathLengthMetersAfterMove`.
- Mathlib phase: `Real.Angle` from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.

## Local abstractions introduced

- `Amplitude` remains an abstract type because the problem names a common amplitude `a` but gives neither a unit nor a scalar calibration. This avoids collapsing a physical amplitude to `ℝ`.
- `AcousticLength`, `AcousticFrequency`, and `AcousticSpeed` are aliases only to Physlib dimensionful types, not scalar aliases.
- `ThreeSpeakerInterferenceSetup` preserves source labels, planar geometry, dimensionful measurements, phases, amplitudes, and the wavelength as distinct physical roles.
- `ProducesMaximumAmplitudeAtListener` is local because no suitable Mathlib/Physlib acoustics theorem was found. Its integer-wavelength path-difference condition is the physical constructive-interference law and is independent of the requested numerical answer.
- `IsLeastPositiveMaximumDisplacement` makes the intended nearest/first maximum explicit; without it, `1 + 2n` metre moves would give later maxima as well.

## Grounding gaps

- LeanExplore exposed plane/harmonic-wave infrastructure but no ready-made theorem characterizing maximum amplitude of three coherent acoustic point sources by integer-wavelength path differences. The faithful local predicate above fills this gap.
- The `archon` executable advertised for DAG navigation was not available on
  `PATH`, so no dependency-graph result was used.
- `.archon/AGENTS.md` was absent in this project checkout; the available `.archon/prover-modes/physics-formalize.md` supplied the matching role discipline.
- No blueprint redraft is requested.

## Verification

The Lean LSP reports no errors and exactly four expected `declaration uses
sorry` warnings for the three supporting lemmas and the target theorem.
`lake env lean PhyXMiniProblems/problem_phyx_mini_0186.lean` also exits with
code 0 and the same four warnings.
