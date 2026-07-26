# Autoformalization result: `problem_phyx_mini_0246.lean`

## Assumption/target split

### Governing laws

- `SatisfiesStraightLineRayGeometry` states the generic geometry of the two rays: the horizontal upper ray equals the forward distance, and the diagonal lower ray satisfies the Pythagorean relation with the forward distance and speaker separation.
- `SatisfiesPathDifferenceLaw` defines the propagation path difference as the absolute difference of the two ray lengths.
- `SatisfiesPropagationPhaseLaw` states the general phase accumulation law `Δφ = Δφ₀ + 2π Δr / λ`.
- `SatisfiesCoherentTwoSourceInterferenceLaw` states the generic coherent-wave law `I = I₁ + I₂ + 2 sqrt (I₁ I₂) cos Δφ` in every coherent `UnitChoices` readout.
- `HasPhysicalAcousticParameters` supplies positivity/nonnegativity needed to select the positive Euclidean path length and to divide by `I₀`; it contains no numerical target coefficient.

### Previous-part results

- There are no results from an earlier subquestion or a dependency chapter.
- Within this file, `ray_lengths_path_difference_and_phase_at_B`, `exact_intensity_at_B`, and `intensity_ratio_at_B_exact` expose the intended later proof route as derived lemmas, all with `by sorry` bodies at the autoformalize stage.

### Figure/data readouts

- `MatchesSourceDescription` records two loudspeakers with a common wavelength, equal abstract acoustic amplitudes, zero initial phase difference, and single-source intensity `I₀` at `B`.
- `MatchesProblemReadouts` records `λ = 1 m`, speaker separation `6 m`, and forward distance `10 m`.
- `MatchesSuppliedFigure` records the primary image geometry: upper/lower sources at `(0, ±3) m`, `A = (10, 0) m`, `B = (10, 3) m`, the upper horizontal ray labeled `r₁`, the lower diagonal ray labeled `r₂`, and the shown distance/wavelength/phase labels.
- `displayedIntensityMultiple` records the four printed coefficients: `0.95`, `1.05`, `0.85`, and `0.75` as exact rational real numbers.

### Current target conclusions

- The exact, unit-independent intensity relation
  `I_B = I₀ * (2 * (1 + cos (2π (sqrt 136 - 10))))`.
- The dimensionless ratio rounds to `19/20 = 0.95` at the nearest hundredth.
- Answer choice `A` is the unique displayed choice matching that rounded ratio.

## Goal-faithfulness audit

The exact interference coefficient, the rounded value `19/20`, and unique choice `A` occur only in derived lemma/theorem conclusions (apart from the unavoidable printed answer-choice lookup table). No setup field stores an answer coefficient. The figure/readout predicates stop at source identity, calibrated lengths, labels, and coordinates. The governing-law structures are general in their paths, phase, and source intensities; none substitutes `sqrt 136 - 10`, `0.95`, or choice `A`. In particular, the combined intensity remains an unconstrained observable until the generic coherent-interference law is assumed.

The printed answer table maps labels to coefficients but does not assert which coefficient matches the physical model. The theorem explicitly concludes `IsUniqueMatchingDisplayedIntensityChoice setup .A`; no local definition aliases the answer to `.A`.

## Source/law/answer audit

- Source and primary image: two in-phase equal-amplitude loudspeakers, separation `6 m`, wavelength `1 m`, `A` centered `10 m` forward, and `B` directly in front of the upper source at the same forward distance. The image explicitly labels the upper horizontal path `r₁`, lower diagonal path `r₂`, and `Δφ₀ = 0 rad`.
- Governing route: straight-line/Pythagorean ray geometry gives `r₁ = 10 m` and `r₂ = √136 m`; the path-difference and propagation-phase laws give `Δr = √136 - 10 m` and `Δφ = 2π(√136 - 10)`; only then does the general coherent-source intensity law determine `I_B`.
- Recorded answer: the resulting exact ratio is `2(1 + cos (2π(√136 - 10)))`, which rounds to `0.95`; this agrees with recorded choice A. The model therefore retains the recorded answer as display metadata and derives its match from the physical laws.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0246:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0246.problem_phyx_mini_0246`.
- Derived proof-route declarations: `ray_lengths_path_difference_and_phase_at_B`, `exact_intensity_at_B`, and `intensity_ratio_at_B_exact`.
- Physical-model declarations: `LengthQuantity`, `SignedLengthQuantity`, `AcousticIntensityQuantity`, `TwoLoudspeakerSetup`, `MatchesSourceDescription`, `MatchesProblemReadouts`, `MatchesSuppliedFigure`, `HasPhysicalAcousticParameters`, `SatisfiesStraightLineRayGeometry`, `SatisfiesPathDifferenceLaw`, `SatisfiesPropagationPhaseLaw`, and `SatisfiesCoherentTwoSourceInterferenceLaw`.
- Answer-model declarations: `intensityRatioAtB`, `roundedToNearestHundredth`, `AnswerChoice`, `displayedIntensityMultiple`, `MatchesDisplayedIntensityChoice`, and `IsUniqueMatchingDisplayedIntensityChoice`.
- The target theorem environment is ready for `\leanok` at the statement level. Per prover write permissions, the blueprint chapter was not edited.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `coherent two-source wave interference intensity phase difference`: returned nearby declarations `ClassicalMechanics.harmonicWave` and `ClassicalMechanics.planeWave` but no acoustic interference-intensity law. Source inspection of `ClassicalMechanics.planeWave` (LeanExplore id `385486`) confirmed that it constructs a vector-valued traveling field and has no received-intensity combination law.
- Natural-language query `unit-independent dimensionful physical quantity with dimensions and unit choices`: selected `Dimensionful` (id `394284`) and `UnitChoices` (id `394255`).
- Likely-name query `Dimensionful WithDim LengthUnit UnitChoices`: confirmed `Dimensionful`, its function coercion, and the unit-scaling API.
- Exact/likely-name queries `WithDim` and `LengthUnit meters SI unit`: selected `WithDim` (id `394425`), `LengthUnit.meters` (id `393154`), and `UnitChoices.SI` (id `394270`).
- Likely-name queries `Real.sqrt` and `Real.cos`, plus natural-language query `round nearest integer`: selected `Real.sqrt` (id `143113`), `Real.cos` (id `128820`), and `round` (id `99909`).

Source/module/docstring data were fetched for each selected declaration before use.

## PhysLean/Mathlib names grounded

- PhysLean/Physlib: `Dimensionful` and `UnitChoices` from `Physlib.Units.Basic`; `WithDim` from `Physlib.Units.WithDim.Basic`; `LengthUnit.meters` from `Physlib.SpaceAndTime.Space.LengthUnit`.
- Mathlib: `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt`; `Real.cos` is declared in `Mathlib.Analysis.Complex.Trigonometric` and is available through the imported `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`; `round` from `Mathlib.Algebra.Order.Round`.
- Physlib dimensions `L𝓭`, `M𝓭`, and `T𝓭` are used to distinguish length from acoustic intensity (`M T⁻³`) rather than collapsing either quantity to `ℝ`.

## Local abstractions introduced

- `AcousticAmplitude` is an abstract type parameter because the problem specifies only equality of source amplitudes, not a scalar unit or amplitude calibration.
- `LoudspeakerInterferenceFigure`, `PlanarPosition`, and the label inductives preserve the primary image's physical and geometric roles.
- The four `Satisfies...` structures are minimal law interfaces for straight-line rays, path difference, propagation phase, and coherent-source intensity. They preserve the physical route to the answer without assuming the requested coefficient.
- Acoustic intensity is a genuine unit-independent dimensionful quantity, not a scalar alias; only explicit readout functions return real numbers.

## Grounding gaps

- LeanExplore found general wave/plane-wave infrastructure but no reusable acoustic two-source intensity-interference law with the needed signature. `SatisfiesCoherentTwoSourceInterferenceLaw` therefore supplies the standard general physical law locally.
- No redraft of the blueprint statement is requested.
- The requested `.archon/AGENTS.md` is absent in this run. The current injected prover instructions and the same project's archived role document were used; this did not affect the authorized write scope.

## Verification

- `archon-lean-lsp` diagnostics: success, with exactly four expected `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0246.lean`: exit code `0`, with the same four expected warnings.
