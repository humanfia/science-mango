# Autoformalization result for `problem_phyx_mini_0200.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSharedHarmonicOscillatorModel` states that the slight web vibrations are linear harmonic oscillations in both configurations.
- Its `spiderOnlyEffectiveMass` and `loadedEffectiveMass` fields identify the two Physlib oscillator masses with coherent-SI readouts of, respectively, spider plus web and spider plus insect plus web.
- Its two stiffness fields state that the same dimensionful web stiffness is used before and after capture.
- Its two angular-frequency fields state only the standard conversion `ω = 2 * π * f`. The dependence `ω = sqrt (k / m)` remains the grounded Physlib definition `ClassicalMechanics.HarmonicOscillator.ω`.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `MatchesProblemData` records spider mass `0.30 g`, insect mass `0.10 g`, negligible web mass (`0 g`), and a spider-only frequency within `1/2 Hz` of the stated approximate `15 Hz`.
- The same predicate records the primary-image geometry: the spider is on the right, the trapped insect is on the left, and the web is a spiral orb.
- `AnswerChoice.hertz` records A=`19`, B=`16`, C=`10`, and D=`13` hertz; `recordedAnswerChoice` records dataset label D.

### Current target conclusions

- `loadedFrequency_matches_recordedAnswerD` concludes that the unknown loaded physical frequency is within `1/2 Hz` of recorded choice D, hence rounds to `13 Hz`.

## Goal-faithfulness audit

- `SpiderWebSetup.loadedFrequency` is an unconstrained physical frequency when the setup is constructed; the setup contains no answer value or answer-choice field.
- `MatchesProblemData` constrains only the given spider-only frequency. It never mentions `loadedFrequency`, `13`, or the recorded answer relation.
- `SatisfiesSharedHarmonicOscillatorModel` contains only effective-mass bookkeeping, equality of the two web stiffnesses, and the general angular/cyclic-frequency conversion. It never mentions `13`, answer D, `MatchesAnswerChoice`, or the target tolerance.
- `AnswerChoice.hertz` is a transcription of displayed source data. `MatchesAnswerChoice` still compares that display data with the independently modeled physical frequency, so unfolding it does not prove the result.
- The target therefore requires the inverse-square-root mass scaling supplied by the two grounded harmonic oscillators; the current conclusion was not smuggled into a hypothesis, structure field, or local definition.

## Declarations and blueprint labels

- Physical types/readouts: `MassQuantity`, `StiffnessQuantity`, `FrequencyQuantity`, `massInKilograms`, `massInGrams`, `stiffnessInNewtonsPerMeter`, and `frequencyInHertz`.
- Figure/setup declarations: `FigureSide`, `WebGeometry`, `SpiderWebSetup`, and `MatchesProblemData`.
- Governing-law interface: `SatisfiesSharedHarmonicOscillatorModel`.
- Answer declarations: `AnswerChoice`, `AnswerChoice.hertz`, `recordedAnswerChoice`, and `MatchesAnswerChoice`.
- `PhyXMiniProblems.ProblemPhyXMini0200.loadedFrequency_matches_recordedAnswerD` corresponds to `thm:physics:phyx_mini_0200:target` and is ready for the statement environment's `\leanok` marker. The blueprint was not edited because prover write permission is limited to the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

- `physical SI quantities mass frequency hertz units`: found `UnitChoices.SI`, `UnitChoices.SI_mass`, `MassUnit`, and related unit declarations.
- `natural frequency of a mass spring harmonic oscillator sqrt stiffness divided by mass`: found and used `ClassicalMechanics.HarmonicOscillator`, `ClassicalMechanics.HarmonicOscillator.ω`, and grounded the available lemma `ClassicalMechanics.HarmonicOscillator.ω_sq`.
- `PhysLean Units Mass Frequency hertz kilogram gram`: found `MassUnit.grams`; it was inspected but not used as a physical mass type because it represents a choice of mass unit rather than a mass quantity.
- `Dimensionful WithDim physical quantity unit-independent value` and `WithDim`: found and used `Dimensionful` and `WithDim`.
- `spring constant stiffness dimension mass time inverse squared`: confirmed the oscillator candidates but found no dedicated dimensionful stiffness quantity.
- `Dimension.M mass dimension time dimension T inverse` and `Dimension.M𝓭`: found and used `Dimension.T𝓭` and `Dimension.M𝓭`.
- Source, module, and docstring data were fetched for the used candidates `ClassicalMechanics.HarmonicOscillator`, `.ω`, `Dimensionful`, `WithDim`, `UnitChoices.SI`, `Dimension.T𝓭`, and `Dimension.M𝓭`. The source of `.ω_sq` was also fetched to confirm the exact `ω^2 = k/m` law.

## PhysLean/Mathlib names grounded

- `Physlib.ClassicalMechanics.HarmonicOscillator.Basic`: `ClassicalMechanics.HarmonicOscillator`, `ClassicalMechanics.HarmonicOscillator.ω`, and `ClassicalMechanics.HarmonicOscillator.ω_sq`.
- `Physlib.Units.Basic`: `Dimensionful` and `UnitChoices.SI`.
- `Physlib.Units.WithDim.Basic`: `WithDim`.
- `Physlib.Units.Dimension`: `Dimension.M𝓭` and `Dimension.T𝓭`.
- Mathlib's `Real.pi`, `Real.sqrt` (through Physlib's `.ω` definition), real absolute value, and `NNReal` infrastructure are used through the imports.

## Local abstractions introduced

- `FigureSide` and `WebGeometry` preserve the image's qualitative labels without pretending they are scalar measurements.
- `StiffnessQuantity` is the minimal Physlib dimensionful type with dimension `M * T⁻¹ * T⁻¹`, i.e. newtons per metre. This avoids treating web stiffness as a bare real.
- `SatisfiesSharedHarmonicOscillatorModel` is an adapter from dimensionful experiment quantities to Physlib's scalar harmonic-oscillator model. It preserves the shared-web-stiffness law and the two physical load configurations.
- The half-hertz relations model the source's whole-hertz precision and the word "about"; they do not identify an approximate physical result with an exact integer.

## Grounding gaps

- LeanExplore exposed a scalar `ClassicalMechanics.HarmonicOscillator` but no ready-made dimensionful mass-spring oscillator or dimensionful stiffness alias. The file therefore retains dimensionful mass, stiffness, and frequency quantities and connects their SI readouts explicitly to the grounded oscillator API.
- The requested `.archon/AGENTS.md` is absent in this project snapshot. The active `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`, and the archived project role document all agree that the prover must not edit blueprint chapters.
- The `archon` executable was not available on `PATH`, so the optional read-only DAG query could not be run. The chapter declares no prerequisite blueprint lemmas.

## Verification

- `archon-lean-lsp` diagnostics: no errors; only the expected `declaration uses sorry` warning at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0200.lean`: succeeded with the same single expected sorry warning.
- `git diff --check` on the two owned output paths: clean.
