# Autoformalization result for `problem_phyx_mini_0313.lean`

This is the genuine post-formalization report for Archon iteration 003. The
chapter contains `% archon:physics`, so the `physics-formalize` discipline
was used. The exact final-review gate reason was evidence-only: it said that no
genuine post-formalization report established the searches and candidates
actually used, grounded library names, local abstractions, grounding gaps, or
the source/law/answer split. It did not identify a semantic defect in the Lean
statement.

I re-audited the existing Lean file against the full chapter, source JSON, and
primary bitmap. It contains no `/- USER: ... -/` comment. Because the physical
model is faithful and the gate failure was evidence-only, iteration 003
retains its declarations and signatures unchanged and regenerates this report
from work actually performed in this run.

## Assumption/target split

### Governing laws

- `SatisfiesCollinearRayGeometry.rayLength` states the collinear ray law:
  because `P` is to the right, each nonnegative path-length readout is the
  signed coordinate difference `x_P - x_source` in every length unit.
- `SatisfiesMonochromaticPropagation.phaseAtP` states the propagation law
  `φ_P = φ_source - 2π r / λ`. Phases lie in `Real.Angle`, so equality is
  equality modulo a full turn.
- `SatisfiesNegligibleAttenuation.receivedAmplitude` is the stated
  approximation that each source's displacement amplitude is unchanged on
  reaching `P`.
- `SatisfiesCoherentPhasorSuperposition.netAmplitudeMagnitude` is the general
  coherent-superposition law: the net amplitude is the Euclidean magnitude of
  the sums of all received cosine and sine components. The law is uniform in
  the four received amplitudes and phases.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `SourceLabel` preserves `S1`, `S2`, `S3`, and `S4`.
  `PointSoundSource` preserves a source's wavelength, longitudinal
  displacement amplitude, initial phase, and radiation pattern.
- `MatchesFourSourceFigure` records the image order
  `S1 < S2 < S3 < S4 < P` and exactly the three source-to-source gaps
  labelled `d`. It deliberately imposes no value on the unlabelled
  `S4`-to-`P` distance.
- `HasIdenticalCoherentPointSources` records that all four sources are
  isotropic and share wavelength `λ`, displacement amplitude `s_m`, and
  initial phase. It does not assume equal arrival phase.
- `SpacingEqualsWavelength` is exactly the question datum `d = λ`.
- `HasPhysicalParameters` records positivity/nondegeneracy of `d`, `λ`,
  `s_m`, and every source-to-`P` path.
- `AnswerChoice.amplitudeMultiplier` transcribes A=1, B=2, C=3, D=4.
  `recordedAnswerChoice` separately records the dataset answer label D.

### Current target conclusions

- `problem_phyx_mini_0313` concludes, in every selected length unit, that
  the physical net displacement amplitude at `P` is
  `4 * amplitudeReadout ... s_m`.
- It also concludes that the recorded choice D is the unique displayed choice
  whose multiplier matches the physical net amplitude.

## Goal-faithfulness audit

- `FourSourceSoundSetup.netAmplitudeAtP` is an independent physical
  observable; no setup field or local definition assigns it `4 s_m`.
- No figure predicate, source predicate, positivity premise, ray law,
  propagation law, or attenuation law mentions factor four, answer D,
  `MatchesDisplayedAmplitudeChoice`, or the theorem conclusion.
- `SatisfiesCoherentPhasorSuperposition` contains unsimplified finite sums of
  arbitrary received phasors. Obtaining `4 s_m` still requires deriving
  whole-wavelength path differences, equal arrival phases, equal unattenuated
  amplitudes, the four-term sum, and the trigonometric magnitude.
- `MatchesDisplayedAmplitudeChoice` is generic in an arbitrary choice.
  `recordedAnswerChoice = .D` is only metadata and cannot establish that D
  matches.
- The substantive intermediate conclusions are theorem-side obligations in
  `rayPathDifferencesAreWholeWavelengths`, `allReceivedPhasesAgree`, and
  `coherentPhasorComponents`; they are not premise fields.
- Wavelengths, paths, coordinates, and acoustic displacement amplitudes are
  not transparent scalar aliases. Nonnegative physical lengths/amplitudes use
  `Dimensionful (WithDim L𝓭 NNReal)`; signed coordinates use
  `Dimensionful (WithDim L𝓭 ℝ)`. Real numbers occur only as explicitly
  unit-labelled readouts, phase components, and dimensionless multipliers.

## Source/law/answer audit

- The primary image `phyx_data/test_image/313.png` was inspected directly.
  It shows `S1`, `S2`, `S3`, `S4` left-to-right, three adjacent gaps
  labelled `d`, and `P` to the right. It supplies no `S4`-to-`P`
  distance, matching `MatchesFourSourceFigure`.
- The source JSON states four uniformly spaced isotropic point sources with
  common wavelength, amplitude, and emission phase, negligible amplitude
  decrease, and the condition `d = λ`. It records D, `4 s_m`, and no
  previous parts.
- The recorded answer remains separate from the governing laws. The intended
  derivation is: equal spacing plus `d = λ` gives integral-wavelength path
  differences; monochromatic propagation gives equal arrival phases;
  negligible attenuation gives four equal amplitudes; generic phasor
  superposition then yields `4 s_m`.

## Declarations and blueprint labels

All current public declarations were retained; iteration 003 added, removed,
or renamed none.

- `LengthQuantity`,
  `def:physics:phyx-mini-0313:phyxminiproblems-problemphyxmini0313-lengthquantity`.
- `SignedLengthQuantity`,
  `def:physics:phyx-mini-0313:phyxminiproblems-problemphyxmini0313-signedlengthquantity`.
- `AcousticDisplacementAmplitude`,
  `def:physics:phyx-mini-0313:phyxminiproblems-problemphyxmini0313-acousticdisplacementamplitude`.
- `lengthReadout`, `signedLengthReadout`, and `amplitudeReadout`,
  respectively the blueprint labels ending in `-lengthreadout`,
  `-signedlengthreadout`, and `-amplitudereadout`.
- `SourceLabel`, `RadiationPattern`, and `PointSoundSource`,
  respectively the labels ending in `-sourcelabel`,
  `-radiationpattern`, and `-pointsoundsource`.
- `FourSourceSoundSetup`, `MatchesFourSourceFigure`,
  `HasIdenticalCoherentPointSources`, `SpacingEqualsWavelength`, and
  `HasPhysicalParameters`, respectively the labels ending in
  `-foursourcesoundsetup`, `-matchesfoursourcefigure`,
  `-hasidenticalcoherentpointsources`, `-spacingequalswavelength`, and
  `-hasphysicalparameters`.
- `SatisfiesCollinearRayGeometry`,
  `SatisfiesMonochromaticPropagation`,
  `SatisfiesNegligibleAttenuation`, and
  `SatisfiesCoherentPhasorSuperposition`, respectively the labels ending in
  `-satisfiescollinearraygeometry`,
  `-satisfiesmonochromaticpropagation`,
  `-satisfiesnegligibleattenuation`, and
  `-satisfiescoherentphasorsuperposition`.
- `rayPathDifferencesAreWholeWavelengths`,
  `allReceivedPhasesAgree`, and `coherentPhasorComponents`, respectively
  the lemma labels ending in `-raypathdifferencesarewholewavelengths`,
  `-allreceivedphasesagree`, and `-coherentphasorcomponents`.
- `AnswerChoice`, `AnswerChoice.amplitudeMultiplier`,
  `recordedAnswerChoice`, `MatchesDisplayedAmplitudeChoice`, and
  `IsUniqueMatchingDisplayedChoice`, respectively the definition labels
  ending in `-answerchoice`, `-answerchoice-amplitudemultiplier`,
  `-recordedanswerchoice`, `-matchesdisplayedamplitudechoice`, and
  `-isuniquematchingdisplayedchoice`.
- `PhyXMiniProblems.ProblemPhyXMini0313.problem_phyx_mini_0313` corresponds
  to `thm:physics:phyx_mini_0313:target`.

The target and topology declarations are ready for statement-environment
`\leanok` markers. The blueprint was not edited because this prover's
explicit write boundary permits only the assigned Lean file and this report.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language dimensional query
  `dimensionful physical quantity with dimension of length and selectable units`
  and likely-name queries `WithDim Dimensionful LengthUnit`, `WithDim`,
  `LengthUnit`, `L𝓭 physical dimension length`, and `UnitChoices.SI`
  found the actual names used in the file:
  `Dimensionful` (id 394284, module `Physlib.Units.Basic`),
  `WithDim` (394425, `Physlib.Units.WithDim.Basic`),
  `LengthUnit` (393137,
  `Physlib.SpaceAndTime.Space.LengthUnit`), `Dimension.L𝓭` (394324,
  `Physlib.Units.Dimension`), and `UnitChoices.SI` (394270,
  `Physlib.Units.Basic`). Source, module, and docstring were fetched for
  these candidates before retaining them.
- Queries `real angle modulo two pi with sine and cosine` and
  `Real.Angle` found `Real.Angle` (146415),
  `Real.Angle.sin` (146462), and `Real.Angle.cos` (146465), all in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`. Their source,
  module, and docstrings were fetched. In particular, `Real.Angle` is
  `AddCircle (2 * π)`, which grounds the modulo-full-turn phase model.
- Queries `Real.sqrt` and
  `Real.sqrt squared sine cosine magnitude` found and retained
  `Real.sqrt` (143113, `Mathlib.Analysis.Real.Sqrt`); its source, module,
  and docstring were fetched.
- Query `NNReal nonnegative real numbers` found `NNReal` (211536,
  `Mathlib.Data.NNReal.Defs`), whose source and module were fetched. It
  grounds nonnegative path lengths and amplitudes.
- Queries `finite sum over a Fintype` and
  `Finset.univ sum over all elements of a Fintype` found
  `Finset.univ` (205948, `Mathlib.Data.Fintype.Defs`); source and module
  were fetched. This grounds the `∑ label : SourceLabel` notation over the
  derived four-element `Fintype`.
- The concept searches
  `coherent phasor superposition magnitude of sum of amplitudes and phases`
  and
  `isotropic acoustic point source sound wave wavelength amplitude phase propagation superposition`
  returned near matches such as `ClassicalMechanics.planeWave`,
  `ClassicalMechanics.harmonicWave`, harmonic-oscillator amplitude/phase
  objects, electromagnetic waves, and generic complex norm lemmas. None is an
  isotropic acoustic point-source model or a four-source acoustic
  superposition law, so none was substituted for the faithful local
  interfaces.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `UnitChoices.SI`, and `LengthUnit`.
- Mathlib: `NNReal`, `Real.Angle`, `Real.Angle.sin`,
  `Real.Angle.cos`, `Real.sqrt`, `Finset.univ`, finite big-operator
  notation, and derived `Fintype` support.

## Local abstractions introduced

- `RadiationPattern` and `PointSoundSource` are the smallest local source
  model preserving isotropy, wavelength, physical displacement amplitude, and
  source phase. The available wave APIs are plane/time-harmonic or
  electromagnetic near matches, not isotropic acoustic point sources.
- `FourSourceSoundSetup` keeps signed source coordinates, nonnegative path
  lengths, emitted/received physical amplitudes, phases, and the independent
  net-amplitude observable distinct.
- `MatchesFourSourceFigure`, `HasIdenticalCoherentPointSources`, and
  `HasPhysicalParameters` isolate source/figure readouts from governing
  physics.
- The four `Satisfies...` structures faithfully expose the needed collinear
  geometry, monochromatic phase propagation, negligible attenuation, and
  generic phasor-superposition laws without assuming the current answer.

## Grounding gaps and redraft requests

- No Mathlib/Physlib API matching coherent superposition of isotropic acoustic
  point sources was found. The local abstract source and law interfaces
  preserve all physical roles needed by the problem and are preferable to a
  scalar placeholder.
- The requested current-checkout file `.archon/AGENTS.md` is absent. The
  injected prover-role instructions, `.archon/PROGRESS.md`, and the archived
  project role document consistently establish the read/write discipline used
  here.
- Although the prompt says `archon` is on `PATH`, both read-only
  `dag-query node` and `dag-query ancestors` attempts returned
  `archon: command not found`. This is not a Lean or modeling blocker; the
  source report has no previous parts.
- No Lean statement redraft is requested. The blueprint's target proof
  paragraph is still only an autoformalization instruction; a
  blueprint-authorized plan/review agent may optionally expand it with the
  whole-wavelength-path, equal-phase, and aligned-phasor derivation above.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly four expected
  `declaration uses sorry` warnings, for the three derived lemmas and final
  theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0313.lean` exited 0 with
  the same four expected warnings.
- A direct `lake build PhyXMiniProblems.problem_phyx_mini_0313` target is
  unavailable because this project's Lake configuration exposes only the
  `PhyxMiniRun` library target; direct Lean compilation is therefore the
  file-specific verification.
