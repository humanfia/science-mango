# Autoformalization result: `problem_phyx_mini_0294.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSinusoidalTravelingWaveLaw` gives each component the common
  traveling-wave form
  `y_m * sin (k*x + temporalPhaseSign direction * omega*t + phi_i)` in
  explicitly selected length and time units.
- `SatisfiesLinearSuperposition` states that the resultant displacement is
  the sum of the two component displacements.
- `IdentifiesResultantAmplitude` represents that same sinusoidal resultant
  with its unknown physical amplitude and the mean component phase. It is a
  general equal-amplitude interference convention and contains no numeric
  phase or amplitude answer.
- `SatisfiesWaveKinematics` states `k*lambda = 2*pi`, `d = v*Delta t`, and
  `omega = k*v` in coherent unit readouts.
- `HasPhysicalWaveParameters` supplies positivity/nondegeneracy and the
  principal phase convention `phi_2 in [0, pi]`. The latter selects the
  physically intended inverse-cosine branch without specifying `phi_2`.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- The component waves share a single amplitude, wavelength, wave number,
  angular frequency, speed, and propagation direction through
  `StringWaveInterferenceSetup`; their phase readouts remain separate.
- Each component amplitude is `9.00 mm`, and the first phase is zero.
- The horizontal and vertical axes are labeled `x` and `y`; label `A` is on
  the solid snapshot, while the shifted snapshot is dashed.
- The arrow and observed propagation point toward negative `x`.
- Valley `A` shifts by `-d`, with `d = 56.0 cm`, between snapshots separated
  by `8.0 ms`; the labeled positions are required to be resultant valleys.
- Adjacent horizontal ticks are `10 cm`, and the primary image shows one
  wavelength spanning four tick intervals.
- The vertical arrow `H = 8.0 mm` is explicitly interpreted as the full
  crest-to-trough height, hence twice the still-unknown resultant amplitude.

### Current target conclusions

- `wavelengthInCentimeters_eq_forty` derives the figure wavelength `40 cm`.
- `waveSpeedInCentimetersPerMillisecond_eq_seven` derives the observed
  feature speed `7 cm/ms`.
- `temporalPhaseSign_eq_one` derives the plus sign in front of `omega*t`
  from negative-`x` propagation.
- `resultantAmplitudeInMillimeters_eq_four` derives the resultant amplitude
  `4 mm` from the peak-to-trough height.
- `resultantAmplitudeReadout_eq` derives the general equal-amplitude
  interference relation rather than assuming it numerically.
- `secondPhaseRadians_eq` derives the exact principal phase
  `phi_2 = 2 * Real.arccos (2/9)`.
- `secondPhaseRoundsToChoiceD` derives agreement to the nearest hundredth
  with `2.69 rad`, answer D.
- `problem_phyx_mini_0294` packages the requested propagation sign, exact
  phase, and displayed answer classification.

## Goal-faithfulness audit

`StringWaveInterferenceSetup.phaseRadians .second` is an independent unknown
real field. No setup field, readout premise, physical-parameter premise, or
governing-law field assigns it `2 * Real.arccos (2/9)`, `2.69`, or answer D.
The only premise restricting it is the standard principal interval
`[0, pi]`, which is needed to choose one phase from the cosine symmetry.

The numeric hypotheses constrain source/figure data only: component
amplitude, `phi_1`, travel distance/time, `H`, and tick spacing. The
resultant amplitude is not numerically assumed; `heightIsPeakToTrough` gives
only its physical relation to `H`. Likewise, the amplitude-interference
premises are symbolic in the unknown component phases and amplitudes. Their
combination still requires the substantive derivation
`cos (phi_2/2) = 2/9` and inversion on the principal branch.

`displayedPhaseRadians` merely records all four supplied answer values, and
`RoundsToDisplayedPhase` is a generic error-bound predicate. Unfolding them
does not prove that the unknown phase matches D. The occurrences of the
exact inverse-cosine phase are confined to lemma/theorem conclusions (and
their explanatory comments). The mapping from negative direction to the
plus temporal sign is the conventional definition for a traveling sine;
it does not encode the requested second-phase answer.

## Declarations created and blueprint labels

- Physical quantity/readout layer: `LengthQuantity`,
  `SignedLengthQuantity`, `TimeQuantity`, `WaveNumberQuantity`,
  `AngularFrequencyQuantity`, `SpeedQuantity`, and their unit-indexed
  readout functions.
- Figure labels and roles: `ComponentWave`, `WaveSnapshot`, `CurveStyle`,
  `FigureAxis`, `HorizontalDirection`, `temporalPhaseSign`,
  `ResultantWaveFigure`, and `IsResultantValleyAt`.
- Physical model and premises: `StringWaveInterferenceSetup`,
  `MatchesProblemAndFigureReadouts`, `HasPhysicalWaveParameters`,
  `SatisfiesWaveKinematics`, `SatisfiesSinusoidalTravelingWaveLaw`,
  `SatisfiesLinearSuperposition`, and `IdentifiesResultantAmplitude`.
- Answer representation: `PhaseAnswerChoice`, `displayedPhaseRadians`, and
  `RoundsToDisplayedPhase`.
- Derived declarations: `equalAmplitudeSineSuperposition`,
  `resultantAmplitudeReadout_eq`, `wavelengthInCentimeters_eq_forty`,
  `waveSpeedInCentimetersPerMillisecond_eq_seven`,
  `temporalPhaseSign_eq_one`,
  `resultantAmplitudeInMillimeters_eq_four`, `secondPhaseRadians_eq`, and
  `secondPhaseRoundsToChoiceD`.
- Blueprint target `thm:physics:phyx_mini_0294:target`:
  `problem_phyx_mini_0294`.

## LeanExplore queries/candidates actually used

Every search used package filters `Mathlib` and `Physlib`.

- `sinusoidal traveling wave interference equal amplitudes phase difference
  resultant amplitude` found `ClassicalMechanics.harmonicWave` and harmonic
  oscillator amplitude/phase declarations, but no two-wave string
  interference or superposition-amplitude law.
- `wave number angular frequency wavelength traveling wave` again found
  `ClassicalMechanics.harmonicWave` and `ClassicalMechanics.planeWave`.
  Source inspection showed that `harmonicWave` is a generic cosine plane
  wave over `Space d`; it does not model two unit-aware scalar string waves,
  figure snapshots, or their resultant phase relation, so it was not used.
- `physical dimensionful quantities length time speed units readout` found
  and grounded `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`,
  and `DimSpeed`.
- `Dimension.L𝓭 Dimension.T𝓭 WithDim` found `Dimension.L𝓭`,
  `WithDim`, and the dimension API used for length, inverse length, time, and
  inverse time.
- `LengthUnit centimeters millimeters` found `LengthUnit`,
  `LengthUnit.centimeters`, and `LengthUnit.millimeters`.
- `TimeUnit seconds milliseconds` found `TimeUnit`, `TimeUnit.seconds`, and
  `TimeUnit.milliseconds`.
- `inverse cosine arccos cosine principal interval` found and grounded
  `Real.arccos`, `Real.arccos_eq_of_eq_cos`, `Real.arccos_cos`, and
  `Real.cos_arccos`. The formalization statement uses `Real.arccos`; the
  inverse lemmas identify the intended later proof route.

Source, module, and docstring details were fetched for `Dimensionful`,
`WithDim`, `Dimension.L𝓭`, `DimSpeed`, the millimeter/centimeter and
second/millisecond unit constants, `Real.arccos`,
`Real.arccos_eq_of_eq_cos`, and the nearby
`ClassicalMechanics.harmonicWave` candidate.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful` from `Physlib.Units.Basic`; `WithDim` and the
  dimension tags from `Physlib.Units.WithDim.Basic`/`Dimension`;
  `DimSpeed` from `Physlib.Units.WithDim.Speed`; `UnitChoices.SI`;
  `LengthUnit.meters`, `.centimeters`, `.millimeters`; and
  `TimeUnit.seconds`, `.milliseconds`.
- Mathlib: real sine/cosine, `Real.pi`, and `Real.arccos` from
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse`, together with
  `Set.Icc` for the principal phase interval.

Lengths, signed coordinates, times, wave number, angular frequency, and
speed are dimension-tagged physical quantities. Bare real numbers are used
only for explicitly selected unit readouts, phase angles, and dimensionless
trigonometric expressions.

## Local abstractions introduced

- `ResultantWaveFigure` preserves axis labels, solid/dashed curve roles,
  label `A`, the direction arrow, both labeled-valley coordinates, `d`, `H`,
  and tick spacing from the primary image.
- `StringWaveInterferenceSetup` preserves the two component identities,
  shared physical wave parameters, separate phases, observable displacement
  functions, snapshot times, and the resultant amplitude.
- The premise structures separate raw figure/data observations,
  physical-domain conditions, kinematics, traveling-wave behavior, linear
  superposition, and resultant-amplitude identification.
- These local abstractions are necessary because the available generic
  Physlib plane-wave object does not represent this one-dimensional,
  two-component, unit-aware string-interference experiment.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration was found for equal-amplitude sinusoidal
  string-wave interference, the phase-difference amplitude formula, or this
  figure/snapshot geometry. Those notions are stated explicitly as local
  interfaces and derived lemmas rather than replaced by scalar aliases.
- The blueprint chapter preserves the source but its proof paragraph is only
  a meta-level autoformalization instruction. A plan-agent redraft should
  record the physical derivation: the image gives resultant amplitude
  `H/2 = 4 mm`, hence `4 = 2*9*cos(phi_2/2)`, and the principal phase is
  `2*arccos(2/9)`, which rounds to `2.69 rad`.
- The auxiliary caption's description of `d` as a repeat distance conflicts
  with the problem text and primary image. Following the explicit instruction
  to use the image as primary evidence, `d` is modeled as the negative-`x`
  displacement of valley `A`; the wavelength instead spans four `10 cm`
  tick intervals.
- The requested `.archon/AGENTS.md` file and advertised `archon` executable
  were absent. The checked-in `.archon/prover-modes/physics-formalize.md`,
  `PROGRESS.md`, source report, and user-supplied instructions were used.
- The assigned Lean file did not previously exist, so there were no
  file-specific `/- USER: ... -/` comments.

## Verification

- `archon-lean-lsp` reports only nine expected `declaration uses sorry`
  warnings and no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0294.lean` exits
  successfully with those same nine expected warnings.
- `git diff --no-index --check` passes for both newly created files.
- The blueprint chapter was not edited to add `\leanok` because the explicit
  write permissions prohibit editing blueprint chapters. A blueprint-owning
  agent should add `\leanok` to `thm:physics:phyx_mini_0294:target` after
  accepting this formalization.
