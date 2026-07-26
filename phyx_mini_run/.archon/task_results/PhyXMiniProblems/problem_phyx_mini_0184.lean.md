# Autoformalization result: `problem_phyx_mini_0184.lean`

This is the genuine post-formalization report requested by the iteration-003
review gate. The exact gate reason is evidence-only: the revised Lean model
predated a report recording the searches and modeling audit actually used.
Accordingly, after re-reading the source report, primary image, physics-marked
blueprint chapter, and Lean file, I preserved the current physical statement.
No semantic defect requiring a redraft was found.

The requested run-local `.archon/AGENTS.md` is absent. As directed by the
iteration-003 plan, I read the canonical archived copy at
`phyx_mini_archives/20260722-review3-rerun/.archon/AGENTS.md`; it confirms that
provers do not edit blueprint chapters and that `\leanok` is applied by the
deterministic sync phase. There is no `/- USER: ... -/` comment in the assigned
Lean file.

## Physical model extracted

- The fixed outer tube and movable insert are each marked `40 cm`; their axial
  overlap makes the total acoustic-column length `L` vary from `40 cm` through
  `80 cm`.
- The primary image places the tuning fork by the left opening and depicts an
  open acoustic column at both ends.
- Standing waves occur at total lengths `42.5 cm`, `56.7 cm`, and `70.9 cm` as
  the insert is pulled out. The source gives sound speed `343 m/s`.
- The physical quantities are the component and total lengths, common end
  correction, wavelength, tuning-fork frequency, and sound speed. Length has
  dimension `L`, frequency has dimension `T⁻¹`, and speed has dimension
  `L T⁻¹`; scalar reals are only named unit readouts and printed answer data.
- The open-open standing-wave law is `2 (L + e) = n λ`. Consecutive observed
  resonances have consecutive longitudinal mode numbers, so the common end
  correction cancels and `λ = 2(56.7 - 42.5) cm = 0.284 m`.
- The nondispersive acoustic relation `v = λ f` then gives
  `f = 343 / 0.284 Hz = 85750 / 71 Hz = 343 / 284 kHz`, approximately
  `1.208 kHz`.
- None of the four printed choices is this value. In particular, the recorded
  dataset answer `D = 12.1 kHz` is inconsistent with the supplied resonance
  spacings and speed and is retained only as metadata.

## Assumption/target split

### Governing laws

- `SatisfiesOpenTubeResonanceLaw setup` supplies the generic effective-length
  mode relation at every observed standing wave and the consecutive-mode rule
  for successively pulled-out resonances. It contains no numerical wavelength
  or frequency.
- `SatisfiesAcousticWaveSpeedLaw setup` supplies the generic relation
  `v = λ f` in compatible length/time units. It contains no requested
  numerical frequency.
- `HasPhysicalAcousticParameters setup` supplies positivity/nondegeneracy of
  speed, wavelength, frequency, total lengths, and mode numbers only.

### Previous-part results

- None. `reports/phyx_mini/problem_phyx_mini_0184.source.json` has an empty
  `previous_parts` array.

### Figure/data readouts

- `MatchesSuppliedTelescopingTubeFigure setup` records the two `40 cm` labels,
  the total-length label `L`, axial telescoping, both open ends, fork placement,
  the air medium, and the overlap bounds.
- `MatchesProblemAndResonanceReadouts setup` records `42.5 cm`, `56.7 cm`,
  `70.9 cm`, `343 m/s`, and that a standing wave is observed at each listed
  configuration.
- `MatchesSuccessiveResonanceSequence setup` records the observed pull-out
  order. It does not assert a derived spacing.
- `displayedAnswerFrequencyInKilohertz` and `recordedDatasetAnswer` encode the
  printed choices and dataset label as source metadata; neither is a premise.

### Current target conclusions

- `frequencyInHertz setup.tuningForkFrequency = 85750 / 71`.
- `frequencyInKilohertz setup.tuningForkFrequency = 343 / 284`.
- `∀ choice, ¬ MatchesAnswerChoice setup choice`.

## Goal-faithfulness audit

`TelescopingTubeResonanceSetup` stores wavelength, sound speed, fork frequency,
geometric lengths, end correction, and mode numbers as independent data. No
field assigns the target wavelength, frequency, resonance spacing, or answer
choice. The three premise structures for figure/readout/order information only
record source observations. The two law structures state generic physical laws,
not the requested numerical consequence. Positivity does not determine a
numerical value.

The exact wavelength and frequency appear only in conclusions of derivation
lemmas and in the main theorem conclusion. `MatchesAnswerChoice` merely defines
what it means for the independent physical frequency to equal a printed value;
it does not select a choice. `recordedDatasetAnswer = .D` is never assumed by
the theorem. Thus no current target conclusion is smuggled into a hypothesis,
premise field, law field, or unfolding definition.

## Declarations and blueprint labels

The main declaration is
`PhyXMiniProblems.ProblemPhyXMini0184.problem_phyx_mini_0184`, corresponding to
`thm:physics:phyx_mini_0184:target`.

For compactness below, `D:` abbreviates the blueprint prefix
`def:physics:phyx-mini-0184:phyxminiproblems-problemphyxmini0184-`, and `L:`
abbreviates
`lem:physics:phyx-mini-0184:phyxminiproblems-problemphyxmini0184-`.

- Dimensionful quantities and readouts:
  `LengthQuantity` (`D:lengthquantity`), `FrequencyQuantity`
  (`D:frequencyquantity`), `SpeedQuantity` (`D:speedquantity`),
  `lengthReadout` (`D:lengthreadout`), `frequencyReadout`
  (`D:frequencyreadout`), `speedReadout` (`D:speedreadout`),
  `lengthInMeters` (`D:lengthinmeters`), `lengthInCentimeters`
  (`D:lengthincentimeters`), `frequencyInHertz` (`D:frequencyinhertz`),
  `frequencyInKilohertz` (`D:frequencyinkilohertz`), and
  `speedInMetersPerSecond` (`D:speedinmeterspersecond`).
- Figure vocabulary:
  `TubePart` (`D:tubepart`), `FigureLengthLabel` (`D:figurelengthlabel`),
  `ResonanceObservation` (`D:resonanceobservation`), `TubeEnd` (`D:tubeend`),
  `AcousticBoundaryCondition` (`D:acousticboundarycondition`),
  `InsertMobility` (`D:insertmobility`), `TuningForkPlacement`
  (`D:tuningforkplacement`), and `AcousticMedium` (`D:acousticmedium`).
- Setup, source predicates, and laws:
  `TelescopingTubeResonanceSetup` (`D:telescopingtuberesonancesetup`),
  `MatchesSuppliedTelescopingTubeFigure`
  (`D:matchessuppliedtelescopingtubefigure`),
  `MatchesProblemAndResonanceReadouts`
  (`D:matchesproblemandresonancereadouts`),
  `MatchesSuccessiveResonanceSequence`
  (`D:matchessuccessiveresonancesequence`),
  `HasPhysicalAcousticParameters` (`D:hasphysicalacousticparameters`),
  `SatisfiesOpenTubeResonanceLaw` (`D:satisfiesopentuberesonancelaw`), and
  `SatisfiesAcousticWaveSpeedLaw` (`D:satisfiesacousticwavespeedlaw`).
- Answer metadata:
  `AnswerChoice` (`D:answerchoice`),
  `displayedAnswerFrequencyInKilohertz`
  (`D:displayedanswerfrequencyinkilohertz`), `recordedDatasetAnswer`
  (`D:recordeddatasetanswer`), and `MatchesAnswerChoice`
  (`D:matchesanswerchoice`).
- Proof-route lemmas:
  `lengthInMeters_eq_lengthInCentimeters_div_hundred`
  (`L:lengthinmeters-eq-lengthincentimeters-div-hundred`),
  `soundWavelengthInMeters_eq` (`L:soundwavelengthinmeters-eq`), and
  `tuningForkFrequencyInHertz_eq` (`L:tuningforkfrequencyinhertz-eq`).

All statement environments are ready for the deterministic `sync_leanok`
phase. I did not edit the blueprint because both the active mode and the
canonical prover-role instructions make it read-only for this lane.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- `Dimensionful WithDim LengthUnit TimeUnit UnitChoices` returned and grounded
  `Dimensionful` (id `394284`).
- `DimSpeed physical propagation speed` returned and grounded `DimSpeed`
  (id `394481`) and `WithDim` (id `394425`). It also returned general wave
  declarations such as `ClassicalMechanics.WaveEquation` and
  `ClassicalMechanics.planeWave`; these were not used because they do not state
  the experiment's scalar resonance laws.
- Exact-name searches grounded `LengthUnit` (id `393137`), `TimeUnit`
  (id `393613`), `UnitChoices` (id `394255`), and `UnitChoices.SI`
  (id `394270`).
- `Dimension.L𝓭 Dimension.T𝓭` and `Dimension.T𝓭` grounded
  `Dimension.L𝓭` (id `394324`) and `Dimension.T𝓭` (id `394330`).
- `open open tube standing wave successive resonance wavelength longitudinal
  mode` returned only unrelated topological declarations such as `IsOpen` and
  `openSegment`; it found no compatible acoustic resonance declaration.
- `acoustic wave speed equals wavelength times frequency` returned general
  wave-equation, plane-wave, and harmonic-wave declarations, but no declaration
  expressing the required unit-aware scalar law `v = λ f`.

I fetched source and module data for every selected infrastructure candidate:

- `Dimensionful` and `UnitChoices`/`UnitChoices.SI` are in
  `Physlib.Units.Basic`.
- `WithDim` is in `Physlib.Units.WithDim.Basic`.
- `DimSpeed` is in `Physlib.Units.WithDim.Speed` and its source is the
  dimensionful type `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `LengthUnit` is in `Physlib.SpaceAndTime.Space.LengthUnit`.
- `TimeUnit` is in `Physlib.SpaceAndTime.Time.TimeUnit`.
- `Dimension.L𝓭` and `Dimension.T𝓭` are in `Physlib.Units.Dimension`.

## Physlib/Mathlib names grounded

The compiling file uses the actual Physlib names `Dimensionful`, `WithDim`,
`Dimension.L𝓭`, `Dimension.T𝓭`, `DimSpeed`, `LengthUnit`, `TimeUnit`,
`UnitChoices`, and `UnitChoices.SI`. It also uses Physlib's concrete
`LengthUnit.meters`, `LengthUnit.centimeters`, and `TimeUnit.seconds` unit
choices. Mathlib supplies `NNReal`, `ℝ`, `ℕ`, arithmetic, order, finite
inductive infrastructure, and propositions through the explicit `Mathlib`
import.

## Local abstractions introduced

- Finite inductive types distinguish tube pieces, figure labels, resonance
  observations, tube ends, boundary conditions, insert motion, source
  placement, medium, and answer labels rather than collapsing them into
  unrelated scalars.
- `TelescopingTubeResonanceSetup` associates those labels with independent,
  dimensionful physical quantities and observations. The common end correction
  faithfully captures a configuration-independent open-end offset that cancels
  between successive resonances.
- The three `Matches...` structures separate primary-image facts, numerical
  source readouts, and observation order.
- `SatisfiesOpenTubeResonanceLaw` and `SatisfiesAcousticWaveSpeedLaw` are the
  smallest local governing-law interfaces needed after the API search found no
  compatible Mathlib/Physlib acoustic declarations. They are generic laws and
  do not contain the target numerical answer.

## Grounding gaps and redraft requests

- No Mathlib/Physlib API was found for open-open tube resonance, consecutive
  longitudinal modes, a shared end correction, or the unit-aware scalar
  acoustic relation `v = λ f`; the local law structures remain necessary.
- The dataset's recorded answer `D = 12.1 kHz` conflicts with the source data.
  The formalization intentionally proves the strongest source-supported exact
  result and preserves `D` only as metadata. No Lean redraft is requested.
- The optional `archon dag-query` could not be run because `archon` is not on
  this lane's `PATH`; the source report independently confirms that there are
  no previous-part dependencies.

## Verification

`archon-lean-lsp` reported only four expected `declaration uses sorry`
warnings, at the three proof-route lemmas and the main target. The independent
command

`lake env lean PhyXMiniProblems/problem_phyx_mini_0184.lean`

exited with code `0` and produced the same four warnings with no errors or
failed dependencies.
