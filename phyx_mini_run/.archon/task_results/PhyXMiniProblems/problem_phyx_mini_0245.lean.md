# Autoformalization result: `problem_phyx_mini_0245.lean`

Archon iteration 002 retry. The review-gate reason was: “physics target does
not import Mathlib; autoformalization must be checked in a real Lake/Mathlib
environment, not as a standalone Lean smoke file.” The file now directly
imports `Mathlib.Data.NNReal.Defs`, the Mathlib module providing the `NNReal`
carrier used by its dimensionful length type, and was checked with the
project's Lake environment.

## Assumption/target split

### Governing laws

- `SatisfiesLongitudinalCavityResonanceLaw` states the generic longitudinal two-mirror cavity condition: a physical wavelength forms a standing wave if and only if there is a positive natural mode number `n` such that `2 L = n lambda` in every selected length unit.
- `HasPhysicalLaserParameters` supplies only nondegeneracy: positive mirror separation and positive operating wavelength.
- No law identifies an adjacent mode, fixes a next wavelength, mentions `632.9930 nm`, or selects answer A.

### Previous-part results

- None. The source report has `previous_parts: []`, and the blueprint chapter describes no earlier-part result as a premise.

### Figure/data readouts

- The laser gain medium is helium--neon gas and the emitted light is red.
- The operating physical wavelength has exact nanometre readout `632.9924 nm`, preserving the source's word “precisely.”
- The mirror separation lies in the nearest-`0.001 mm` rounding bin centered on `310.372 mm`.
- The operating wavelength is observed to form a longitudinal standing wave.
- The primary image places a full reflector at the left cavity boundary, a partial reflector at the right boundary, the standing light wave inside the cavity, and the output beam to the right; the beam exits through the right/partial-reflector end. All five printed labels are captured.
- The four displayed answer readouts are A `632.9930 nm`, B `622.9930 nm`, C `642.5693 nm`, and D `630.9130 nm`. The dataset's recorded label A is stored as metadata, not used as a premise.

### Current target conclusions

- There exists a physical wavelength satisfying `IsNextLongerStandingWavelength`: it is resonant, strictly longer than the operating wavelength, and minimal among resonant wavelengths longer than the operating wavelength.
- Its nanometre readout rounds to `632.9930 nm` at resolution `0.0001 nm`.
- It matches displayed choice A, and A is the unique displayed choice matching that rounding bin.

## Goal-faithfulness audit

- `HeliumNeonLaserCavitySetup` has no field for a next wavelength, requested answer, adjacent mode, or numerical result. Its wavelength predicate is independent physical/observational data.
- `MatchesProblemReadouts` contains only the supplied operating wavelength, displayed mirror-spacing measurement, apparatus identity, and current standing-wave observation. It contains no next-mode formula or answer-A claim.
- `SatisfiesLongitudinalCavityResonanceLaw` is quantified over every wavelength and exposes only the standard integer half-wave condition. It does not assume that the next mode is `n - 1`, characterize the next-longer wavelength, or state its numerical value.
- `IsNextLongerStandingWavelength` is a nonnumeric order-theoretic characterization of the requested physical quantity. It is used only in the conclusion and is not a theorem premise.
- `RoundsToDisplayedValue` is a general half-open rounding-bin predicate. It does not make any particular answer true by unfolding.
- `recordedDatasetAnswer` and `displayedAnswerWavelengthInNanometers` reproduce source metadata. The recorded answer is not passed to the theorem, and unfolding the choice table cannot establish resonance or the rounding conclusion.
- The intermediate `operatingModeNumber_is_near_980650` is itself a `sorry`-backed derived lemma, not a premise or local definition. It concludes only that the current mode is one of `980649`, `980650`, or `980651`; it does not state the target wavelength.
- The exact printed decimals would make the ideal law inconsistent if both were imposed as exact equalities: `2 * 310.372 mm / 632.9924 nm` is approximately `980650.0046`, not a natural number. Treating the six-digit mirror spacing as a displayed measurement at `0.001 mm` resolution avoids explosion while retaining an exact resonance law. All compatible current modes yield a next-longer wavelength in the `632.9930 nm` rounding bin.

## Declarations and blueprint correspondence

- Dimensionful role and readouts: `LengthQuantity`, `lengthReadout`, `lengthInNanometers`, `lengthInMillimeters`, and `lengthInMeters`.
- General measurement relation: `RoundsToDisplayedValue`.
- Physical and figure vocabulary: `LaserGainMedium`, `LaserLightColor`, `CavityEnd`, `ReflectorKind`, `FigureElement`, and `FigurePlacement`.
- Independent setup and data predicates: `HeliumNeonLaserCavitySetup`, `MatchesPrimaryLaserFigure`, `MatchesProblemReadouts`, and `HasPhysicalLaserParameters`.
- Governing-law interface: `SatisfiesLongitudinalCavityResonanceLaw`.
- Requested-quantity characterization: `IsNextLongerStandingWavelength`.
- Displayed-answer model: `AnswerChoice`, `displayedAnswerWavelengthInNanometers`, `recordedDatasetAnswer`, and `MatchesDisplayedAnswer`.
- Derived proof-route lemma: `operatingModeNumber_is_near_980650`.
- `problem_phyx_mini_0245` formalizes blueprint label `thm:physics:phyx_mini_0245:target`.

## LeanExplore queries and candidates

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `physical quantity with dimensions length SI unit nanometre millimetre` returned `LengthUnit` (id 393137), `UnitChoices.SI` (id 394270), `Dimension` (id 394292), `Dimension.L𝓭` (id 394324), and `WithDim.scaleUnit_val` (id 394460). Sources/modules were fetched for the candidates used to guide the representation.
- Natural-language query `standing wave wavelength cavity resonance integer half wavelengths` returned `ClassicalMechanics.WaveVector`, `ClassicalMechanics.harmonicWave`, `ClassicalMechanics.WaveEquation`, and plane-wave material, but no two-mirror cavity spectrum or integral half-wave law.
- Likely-name query `Dimensionful WithDim Dimension.L𝓭 UnitChoices.SI` selected `Dimensionful` (id 394284, `Physlib.Units.Basic`) and `UnitChoices.SI` (id 394270, `Physlib.Units.Basic`). `Dimensionful`'s fetched source confirms it is a subtype of unit-dependent functions satisfying the dimensional scaling law.
- Natural-language query `WithDim physical dimension tagged value` selected `WithDim` (id 394425, `Physlib.Units.WithDim.Basic`); its fetched source confirms that it tags an underlying carrier with a physical dimension.
- Likely-name query `LengthUnit.nanometers LengthUnit.millimeters` selected `LengthUnit.nanometers` (id 393157) and `LengthUnit.millimeters` (id 393159), both from `Physlib.SpaceAndTime.Space.LengthUnit`; their fetched sources confirm the `10^-9 m` and `10^-3 m` scales.
- Likely-name query `LengthUnit.meters` did not surface a standalone `meters` result, but the fetched source for `UnitChoices.SI` explicitly sets its length field to `LengthUnit.meters`, and the fetched `LengthUnit` source confirms the positive-scale unit representation.
- Natural-language query `NNReal nonnegative real numbers` selected `NNReal` (id 211536, `Mathlib.Data.NNReal.Defs`); its fetched source confirms that it is the subtype `{r : ℝ // 0 ≤ r}`. This is the directly imported Mathlib carrier used for nonnegative physical lengths.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.meters`, `LengthUnit.millimeters`, and `LengthUnit.nanometers`.
- Mathlib/core numerical infrastructure: `NNReal` from `Mathlib.Data.NNReal.Defs`, plus `ℝ`, `ℕ`, rational numeral notation, inequalities, conjunctions, and existential quantification.

## Local abstractions introduced

- `LengthQuantity` is a dimension-tagged, unit-independent Physlib quantity with a nonnegative carrier. It is not a transparent scalar alias or a one-field scalar wrapper.
- `HeliumNeonLaserCavitySetup` is the smallest local apparatus interface that preserves the gain medium, color, two reflector roles, mirror separation, current wavelength, image labels/placements, beam exit, and the independent standing-wave predicate.
- `SatisfiesLongitudinalCavityResonanceLaw` supplies the missing laser-cavity-specific physical API as a general law. It preserves exact dimensional behavior by requiring the relation in every length unit.
- `RoundsToDisplayedValue` models the finite precision required to reconcile the source decimals and to interpret the trailing zero in the multiple-choice answer.
- The categorical figure types preserve qualitative image evidence without inventing scalar coordinates that the image does not provide.

## Grounding gaps

- LeanExplore found Physlib's general wave, harmonic-wave, dimensional, and unit APIs, but no reusable declaration for longitudinal modes of a two-mirror optical cavity and no ready-made “next resonant wavelength” relation. The local generic resonance-law interface and order characterization fill those gaps without assuming the target answer.
- The `archon` executable advertised for DAG navigation is not available on `PATH` in this checkout, so both requested `dag-query` commands failed before returning graph data.

## Verification and redraft requests

- `archon-lean-lsp` diagnostics report success with only the two expected `declaration uses sorry` warnings, at `operatingModeNumber_is_near_980650` and `problem_phyx_mini_0245`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0245.lean` exits successfully with the same two expected warnings.
- The direct `Mathlib.Data.NNReal.Defs` import and the successful Lake check address the iteration-002 review-gate reason without changing any physical premise or target.
- The cited source report and the primary image `phyx_data/test_image/245.png` were re-read. The image confirms the modeled left full reflector, right partial reflector, interior standing wave, and right-exterior laser beam.
- No file-specific `/- USER: ... -/` comments are present in the assigned Lean file.
- The requested `.archon/AGENTS.md` role file is absent in this checkout; `.archon/prover-modes/physics-formalize.md` was read completely and used as the available role/mode document.
- The blueprint exists and contains `% archon:physics`. It was not edited or marked `\leanok` because this task's explicit write permissions prohibit editing blueprint chapters. A coordinator with blueprint write permission should add `\leanok` to `thm:physics:phyx_mini_0245:target` after accepting the formalization.
- If the intended source semantics require both printed lengths to be exact mathematical equalities, the blueprint should be redrafted because those data contradict the exact integral standing-wave law. The present resolution-based reading is consistent with the answer precision and the recorded choice.
