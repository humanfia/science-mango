# Prover result: `problem_phyx_mini_0217` (iteration 014)

## Outcome

- Replaced all four `sorry` bodies in
  `PhyXMiniProblems/problem_phyx_mini_0217.lean` with sound proofs.
- `shellDiameterInMeters_eq_threeTwentieths` uses the
  `Dimensionful` unit-scaling invariant and the exact
  centimeter-to-meter scale `1/100`.
- `resonantWavelengthInMeters_eq_threeFifths` derives the wavelength
  from the diameter approximation and quarter-wave law.
- `resonantFrequencyInHertz_eq_seventeenHundredThirds` derives the
  frequency from `v = f * wavelength` and the stated `340 m/s` model
  input.
- `problem_phyx_mini_0217` proves the exact frequency and checks all
  four finite answer choices, establishing that choice D (`570 Hz`) is
  uniquely closest.
- No redraft is needed, and no `sorry`, `admit`, custom axiom, or
  `native_decide` remains in the assigned Lean file.

## Validation

- Lean LSP diagnostics: clean.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0217.lean`: exit
  code 0 with no output.
- `lean_verify` reports only Lean's standard foundational axioms
  `propext`, `Classical.choice`, and `Quot.sound`, with no suspicious
  source patterns.

## Project-instruction notes

- `.archon/AGENTS.md` is absent; the explicit prover instructions in
  the task were followed.
- No `/- USER: ... -/` file-specific hint is present.
- The blueprint was not edited because this lane permits writes only
  to the assigned Lean file and this result file. Its theorem and
  helper environments are ready for `\leanok` synchronization.

---

# Prior post-formalization result: `problem_phyx_mini_0217`

- Lean file: `PhyXMiniProblems/problem_phyx_mini_0217.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0217.tex`
- Blueprint target label: `thm:physics:phyx_mini_0217:target`
- Prover mode: `physics-formalize`
- Retry-gate reason resolved: the Lean file now explicitly imports `Mathlib` and was checked with `lake env lean` in the project Lake/Mathlib environment.
- Primary image inspected: `phyx_data/test_image/217.png`.
- No `/- USER: ... -/` file-specific comment was present.

## Assumption/target split

### Governing laws and modeling assumptions

- `UsesFundamentalClosedOpenDiameterApproximation setup` states the model choices needed to extract an acoustic length from the shell: ambient air, an open mouth, an effectively closed inner end, the fundamental mode, ambient-noise excitation, shell-cavity resonance as the perceived mechanism, and effective cavity length equal to shell diameter. It contains no resonant-frequency value and no answer choice.
- `SatisfiesQuarterWaveAcousticLaws setup` states the two governing relations for this idealization: `lambda = 4 L` for the fundamental open--closed cavity and `v = f lambda` for nondispersive sound propagation. The laws are expressed through compatible named-unit readouts and do not state the derived numerical answer.
- `UsesStandardAmbientAirSoundSpeed setup` supplies the conventional elementary estimate `340 m/s`. This value is explicitly separated from the problem statement because neither temperature nor sound speed appears in the source.
- `HasPhysicalAcousticParameters setup` records positivity/nondegeneracy of the modeled length, wavelength, frequency, and speed readouts. It does not determine any of them numerically.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure and source-data readouts

- `MatchesPrimaryFigure setup` records the categorical primary-image evidence: a conch at the listener's ear in an ocean/beach/sky scene and no printed text. The bitmap contains no dimension or frequency label.
- `MatchesProblemStatement setup` records the sole numerical datum in the prose, the shell diameter `15 cm`.
- `displayedAnswerFrequencyHertz` records the four displayed values `510`, `530`, `550`, and `570` Hz.
- `recordedDatasetAnswer = .D` is metadata used only in the theorem conclusion; it is not a theorem premise or a governing-law field.

### Current target conclusions

- `shellDiameterInMeters_eq_threeTwentieths`: the source diameter converts to `3/20 m`.
- `resonantWavelengthInMeters_eq_threeFifths`: the model wavelength is `3/5 m`.
- `resonantFrequencyInHertz_eq_seventeenHundredThirds`: the model frequency is `1700/3 Hz`.
- `problem_phyx_mini_0217`: the model frequency is exactly `1700/3 Hz`, and choice D (`570 Hz`) is uniquely closest among the displayed estimates.

## Goal-faithfulness audit

- `SeashellResonanceSetup` keeps shell diameter, effective cavity length, resonant wavelength, resonant frequency, and sound speed as independent physical fields. No field defines the resonant frequency to be the target value.
- Neither `MatchesPrimaryFigure` nor `MatchesProblemStatement` contains a wavelength, frequency, or answer-choice conclusion.
- The acoustic-law interface contains only the general quarter-wave and wave-speed relations. It does not contain `1700/3`, `570`, `.D`, or the closest-choice proposition.
- The explicit `340 m/s` premise is a conventional ambient-air model input, not the current subquestion's answer. The source/model distinction is documented in the declaration and in this report.
- `recordedDatasetAnswer` is not passed as evidence. The theorem must conclude that this metadata label is closest using the independently modeled frequency and displayed values.
- `displayedAnswerErrorHertz` and `IsClosestDisplayedFrequencyChoice` only define the comparison criterion; unfolding them does not make D closest without the substantive modeled-frequency conclusion.
- The target is therefore not smuggled into a hypothesis, premise structure, law field, satisfaction predicate, or helper definition.

## Declarations and blueprint correspondence

The chapter currently provides the single label `thm:physics:phyx_mini_0217:target`. The principal corresponding Lean declaration is:

- `PhyXMiniProblems.ProblemPhyXMini0217.problem_phyx_mini_0217`.

Public support declarations for that target are:

- Dimensionful quantities/readouts: `AcousticLength`, `AcousticFrequency`, `AcousticSpeed`, `lengthReadout`, `frequencyReadout`, `speedReadout`, `lengthInCentimeters`, `lengthInMeters`, `frequencyInHertz`, `speedInMetersPerSecond`.
- Physical/figure roles: `SeashellKind`, `AcousticMedium`, `ResonatorEnd`, `AcousticBoundaryCondition`, `ResonanceMode`, `AcousticExcitation`, `PerceivedSoundMechanism`, `FigureObject`, `SeashellFigure`, `SeashellResonanceSetup`.
- Premise interfaces: `MatchesPrimaryFigure`, `MatchesProblemStatement`, `HasPhysicalAcousticParameters`, `UsesStandardAmbientAirSoundSpeed`, `UsesFundamentalClosedOpenDiameterApproximation`, `SatisfiesQuarterWaveAcousticLaws`.
- Derived statements: `shellDiameterInMeters_eq_threeTwentieths`, `resonantWavelengthInMeters_eq_threeFifths`, `resonantFrequencyInHertz_eq_seventeenHundredThirds`.
- Answer-data/comparison declarations: `AnswerChoice`, `displayedAnswerFrequencyHertz`, `recordedDatasetAnswer`, `displayedAnswerErrorHertz`, `IsClosestDisplayedFrequencyChoice`.

These helpers all support the same blueprint target; the current blueprint has no separate labels for them.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

### Query: `acoustic frequency sound wave quarter wave closed open resonator`

- Near matches: `ClassicalMechanics.planeWave`, `ClassicalMechanics.harmonicWave`, `ClassicalMechanics.WaveEquation`, and `ClassicalMechanics.WaveVector`.
- These are general wave objects/equations and do not provide the open--closed quarter-wave cavity boundary law needed here, so they were not imported into the model.

### Query: `quarter-wave resonator acoustic wavelength frequency relation`

- Near matches: `ClassicalMechanics.transverseHarmonicPlaneWave`, `ClassicalMechanics.harmonicWave`, `ClassicalMechanics.WaveVector`, and `ClassicalMechanics.planeWave_waveEquation`.
- No dedicated acoustics or quarter-wave resonator declaration was returned.

### Query: `Dimensionful WithDim physical units length frequency`

- Used candidates: `Dimensionful` (`Physlib.Units.Basic`) and `Dimension.L𝓭`.
- Also inspected: `CarriesDimension.toDimensionful` and `UnitChoices.dimScale`; these corroborate the unit-independent dimensional representation but were not referenced directly.

### Query: `WithDim`

- Used candidate: `WithDim` (`Physlib.Units.WithDim.Basic`). Its source is a dimension-tagged structure with an underlying `val`.

### Query: `DimSpeed`

- Used candidate: `DimSpeed` (`Physlib.Units.WithDim.Speed`). Its source defines a unit-independent nonnegative speed with dimension `L𝓭 * T𝓭⁻¹`.
- Related candidates `DimSpeed.oneMeterPerSecond`, `DimSpeed.oneKilometerPerHour`, and `DimSpeed.speedOfLight` were not needed.

### Query: `Dimension.T𝓭 inverse time frequency`

- Used candidate: `Dimension.T𝓭` (`Physlib.Units.Dimension`) together with dimension inversion to model frequency.
- `UnitExamples.cosDim_isDimensionallyCorrect` and `Dimension.inv_time` were relevant examples/lemmas but unnecessary in the declarations.

### Query: `LengthUnit centimeters meters TimeUnit seconds`

- Used candidates: `LengthUnit.centimeters`, `LengthUnit`, `TimeUnit`, and `UnitChoices.SI`.
- Source inspection confirmed that `LengthUnit.centimeters` is `10^-2` meter and that `UnitChoices.SI` uses meters and seconds.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `DimSpeed`, `Dimension.L𝓭`, `Dimension.T𝓭`, `LengthUnit`, `LengthUnit.centimeters`, `LengthUnit.meters`, `TimeUnit`, `TimeUnit.seconds`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, `ℝ`, real arithmetic/order, finite inductive equality, and real absolute value notation used by the displayed-error definition.
- The file explicitly imports both `Mathlib` and `Physlib.Units.WithDim.Speed`.

## Local abstractions introduced

- `AcousticFrequency` is constructed from the grounded unit-independent `Dimensionful (WithDim T𝓭⁻¹ NNReal)` API because no dedicated Physlib acoustic-frequency type was found. This preserves inverse-time dimension and nonnegativity rather than collapsing frequency to a scalar alias.
- The categorical shell, medium, resonator-end, boundary-condition, excitation, mechanism, and figure types preserve the distinct physical roles required by the source and model.
- `SatisfiesQuarterWaveAcousticLaws` is a local law interface because LeanExplore found only general plane/harmonic wave APIs, not a one-dimensional open--closed acoustic resonator law. Its two fields are the governing relations, not the requested numerical result.
- Named real readouts are used only after the underlying lengths, frequency, and speed have been represented by dimensionful Physlib quantities.

## Source/law/answer audit

- Source fact: shell diameter is `15 cm`.
- Primary-image fact: a conch is held at the listener's ear in a beach/ocean scene; the image contains no printed labels.
- Extra model choices: effective cavity length equals shell diameter; the mouth is open, the inner end is effectively closed, and the fundamental quarter-wave mode is used.
- Extra numerical convention: ambient-air sound speed is `340 m/s`.
- Derived physics: `lambda = 4(0.15 m) = 0.60 m` and `f = 340/0.60 = 1700/3 Hz`, approximately `566.7 Hz`.
- Answer audit: among `510`, `530`, `550`, and `570` Hz, `570 Hz` is uniquely closest, agreeing with recorded answer D.

## Grounding gaps

- No dedicated Mathlib/Physlib declaration for an acoustic open--closed quarter-wave resonator or seashell-cavity resonance was found. The faithful local law and role abstractions above remain necessary.
- The source does not state temperature, sound speed, end correction, or detailed cavity geometry. Therefore the exact model value depends explicitly on the stated elementary approximation; the Lean theorem does not present `570 Hz` as a geometry-free consequence of the image alone.

## Verification

- `archon-lean-lsp` diagnostics: no errors; four expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0217.lean`: exit code 0; the same four expected warnings at the three derived lemmas and final theorem.

## Blueprint synchronization note

The chapter already exists and contains `% archon:physics`. It was not edited because the task's final write-permission block permits edits only to the assigned Lean file and this task-result file and explicitly forbids blueprint edits. A blueprint synchronization step should add `\leanok` to `thm:physics:phyx_mini_0217:target` after accepting this formalization, and may add individual helper entries if the project requires every public helper to have its own environment.
