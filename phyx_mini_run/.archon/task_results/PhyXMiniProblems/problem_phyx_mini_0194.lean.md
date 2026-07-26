# Autoformalization result: `problem_phyx_mini_0194`

## Mode and source audit

- The blueprint contains `% archon:physics`, so the `physics-formalize` discipline applies.
- The requested `.archon/AGENTS.md` is absent in this checkout. I used the injected role instructions and the complete `.archon/prover-modes/physics-formalize.md` fallback.
- The assigned Lean file contains no `/- USER: ... -/` comments.
- The primary image shows listener `L` on the left, source `S` on the right, `v_L = 0`, `v_S = 30 m/s`, a rightward-positive `L to S` axis, and the police car moving right. Thus the source recedes from the listener and sound received at `L` propagates leftward.
- The source report lists no previous parts. The advertised `archon dag-query` command is unavailable on `PATH`, so there were no DAG results to use.
- The review-gate reason was: the target did not explicitly import Mathlib and needed checking in a real Lake/Mathlib environment. The redraft now explicitly imports `Mathlib`, retains the Physlib units import, and was checked with `lake env lean`.

## Assumption/target split

### Governing laws

- `SatisfiesLeftwardAcousticDopplerLaw setup` states the one-dimensional classical acoustic Doppler relation for leftward sound. Listener and source velocities are signed along the figure's `L`-to-`S` axis and are measured relative to the air velocity.
- `HasPhysicalDopplerParameters setup` records positive emitted/heard frequency, positive sound speed, and a subsonic source relative to the air. These are admissibility conditions, not a numerical answer.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure setup` records the police-car siren role, `L` left of `S`, `v_L = 0 m/s`, `v_S = +30 m/s`, rightward/receding source motion, and leftward propagation from `S` to `L`.
- `AnswerChoice.hertz` records the displayed choices `267`, `276`, `283`, and `296 Hz`; `recordedAnswerChoice` records dataset metadata label B.
- The image and question omit the emitted siren frequency, still-air condition, and numerical sound speed. Therefore these are not fields of `MatchesProblemAndPrimaryFigure`.

### Explicit auxiliary calibrations

- `UsesStandardStillAir setup` separately assumes air velocity `0 m/s` and sound speed `343 m/s`.
- `UsesNominalSirenEmission setup` separately assumes the nominal emitted frequency `300 Hz` required to reproduce the answer table.
- These premises make the numerical multiple-choice problem well-posed while keeping omitted data distinct from actual figure readouts.

### Current target conclusions

- `heardFrequencyInHertz_eq_exactModelValue` concludes the exact model readout
  `frequencyInHertz setup.heardFrequencyAtL = 102900 / 373`.
- `recedingSiren_matches_recordedAnswerB` concludes that the heard frequency is within `1/2 Hz` of the displayed `276 Hz` choice B, i.e. it rounds to B.

## Goal-faithfulness audit

- `RecedingSirenSetup.heardFrequencyAtL` is an independent dimensionful frequency field. It is not defined as `276 Hz` or as the exact target value.
- `MatchesProblemAndPrimaryFigure` contains no emitted-frequency calibration, sound-speed calibration, answer choice, or constraint on `heardFrequencyAtL`.
- `UsesStandardStillAir` and `UsesNominalSirenEmission` constrain only air/sound-speed and emitted-frequency data respectively; neither states the requested heard frequency.
- `SatisfiesLeftwardAcousticDopplerLaw` states the generic governing formula in terms of independent source, listener, air, speed, emitted-frequency, and heard-frequency quantities. It mentions neither `276`, `102900 / 373`, answer B, nor the rounding predicate.
- `MatchesAnswerChoice` is only the independently defined nearest-whole-hertz tolerance relation. `recordedAnswerChoice := .B` is source metadata, not an assertion that the physics matches B.
- Consequently the exact heard frequency and match with B occur only as conclusions of the lemma/theorem; they were not smuggled into a premise structure or a local definition.

## Declarations and blueprint correspondence

- Target declaration for `thm:physics:phyx_mini_0194:target`:
  `PhyXMiniProblems.ProblemPhyXMini0194.recedingSiren_matches_recordedAnswerB`.
- Supporting derived lemma (the blueprint currently has no separate environment for it):
  `PhyXMiniProblems.ProblemPhyXMini0194.heardFrequencyInHertz_eq_exactModelValue`.
- Dimensionful quantity/readout support:
  `AcousticFrequency`, `AxialPosition`, `AxialVelocity`, `frequencyReadout`,
  `frequencyInHertz`, `positionReadout`, `positionInMeters`,
  `axialVelocityReadout`, `axialVelocityInMetersPerSecond`, and
  `speedInMetersPerSecond`.
- Physical/figure support:
  `FigurePoint`, `SoundSourceKind`, `AxialDirection`, `RecedingSirenSetup`,
  `MatchesProblemAndPrimaryFigure`, `UsesStandardStillAir`,
  `UsesNominalSirenEmission`, `HasPhysicalDopplerParameters`, and
  `SatisfiesLeftwardAcousticDopplerLaw`.
- Answer-table support:
  `AnswerChoice`, `AnswerChoice.hertz`, `recordedAnswerChoice`, and
  `MatchesAnswerChoice`.

The support declarations are public because they expose the assumption/target boundary needed by the later prover. The chapter has only one umbrella target environment, so they do not have individual blueprint labels.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `classical acoustic Doppler effect moving source observer frequency` returned Physlib classical-wave candidates such as `ClassicalMechanics.planeWave` and `ClassicalMechanics.harmonicWave`, but no acoustic Doppler law.
- `DopplerShift dopplerFrequency acousticFrequency` again returned `ClassicalMechanics.planeWave` and unrelated shift declarations, with no Doppler-frequency API.
- `dimensionful physical quantity frequency inverse time SI units speed velocity` returned and motivated use of `Dimensionful`, `UnitChoices.SI`, and `DimSpeed`.
- `Dimensionful WithDim DimSpeed UnitChoices TimeUnit LengthUnit` returned `Dimensionful`, `DimSpeed`, `UnitChoices.dimScale`, and related unit infrastructure.
- `WithDim` returned `WithDim` and its dimension-tagged operations.
- `TimeUnit seconds LengthUnit meters` returned `UnitChoices.SI` and `LengthUnit` candidates.
- `Dimension L𝓭 T𝓭 dimension multiplication inverse` returned `Dimension.L𝓭` and the commutative-group infrastructure for dimension products/inverses.

Source/module details fetched for actual-used candidates:

- `Dimensionful` — `Physlib.Units.Basic`; a subtype of unit-choice-indexed representations satisfying `HasDimension`.
- `WithDim` — `Physlib.Units.WithDim.Basic`; a type tagged by a physical `Dimension`.
- `DimSpeed` — `Physlib.Units.WithDim.Speed`; `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `UnitChoices.SI` — `Physlib.Units.Basic`; selects metres, seconds, kilograms, coulombs, and kelvin.
- `LengthUnit` — `Physlib.SpaceAndTime.Space.LengthUnit`; the physical length-unit scale type.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `DimSpeed`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`,
  `LengthUnit.meters`, `TimeUnit`, and `TimeUnit.seconds`.
- Mathlib: `NNReal`/`ℝ≥0`, `ℝ`, real absolute value notation, and the ordinary ordered-field relations used for SI scalar readouts.

## Local abstractions introduced

- `AcousticFrequency`, `AxialPosition`, and `AxialVelocity` specialize Physlib's dimensional framework. Signed velocity uses `ℝ` under the velocity dimension because `DimSpeed` is intentionally nonnegative and cannot encode the signed figure axis.
- `RecedingSirenSetup` preserves source/listener roles and independent physical quantities without collapsing them to bare scalar aliases.
- The figure and calibration predicates keep image evidence separate from conventional numerical assumptions.
- `SatisfiesLeftwardAcousticDopplerLaw` is the smallest local governing-law interface required because LeanExplore exposed no matching Mathlib/Physlib acoustic Doppler declaration.
- The answer-choice type and tolerance predicate preserve the multiple-choice/rounding semantics rather than asserting an exact integer-valued physical frequency.

## Grounding gaps and redraft requests

- No dedicated acoustic Doppler law was found in Mathlib/Physlib; the faithful local law structure is therefore necessary.
- The supplied problem is numerically underdetermined: neither the emitted source frequency nor the sound speed/air state appears in the text or bitmap. A blueprint redraft should explicitly justify the auxiliary `300 Hz`, still-air, and `343 m/s` calibration if the intended target remains answer B.
- The auxiliary prose caption's final sentence says the car moves *towards* the listener, contradicting both the scenario and the primary image. The formalization follows the primary evidence: the source moves away.
- The blueprint theorem environment contains the generic autoformalization instruction rather than the advertised informal derivation. It should record `f_L = 300 * 343 / (343 + 30) = 102900 / 373 ≈ 275.87 Hz`, hence nearest whole-hertz choice B.
- The blueprint was not edited to add `\leanok` because this task's explicit write permissions prohibit blueprint edits. A blueprint-authorized synchronization step should mark `thm:physics:phyx_mini_0194:target` after accepting the declaration.

## Verification

- `archon-lean-lsp` reports only the two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0194.lean` exits successfully with only those same two expected warnings.
