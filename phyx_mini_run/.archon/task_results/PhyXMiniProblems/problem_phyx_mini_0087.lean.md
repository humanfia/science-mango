# Prover result: `problem_phyx_mini_0087.lean`

## Status

Complete. All three assigned proof obligations are closed, the file is
sorry-free, and every declaration signature is unchanged.

## Proof summary

- `source_paths_to_P1_are_equal`: expands Physlib's Euclidean `Space 2`
  distance with `Space.dist_eq` and `Fin.sum_univ_two`; the stated coordinates
  reduce both source-to-`P₁` distances to the same square root.
- `path_difference_to_P2_in_wavelengths`: the same coordinate reduction gives
  the exact path lengths `1360 nm` and `80 nm`; their difference divided by
  `400 nm` is `16/5`.
- `phaseDifferenceAtP2_eq_recordedAnswerC`: propagation at `P₁` and the equal
  paths turn the measured lead into the relative emission phase. Propagation
  at `P₂`, together with the proved `16/5` path difference, then reduces the
  unwrapped phase lead to `29/10`, answer C.

## Blueprint marker readiness

The theorem proof and both geometry-lemma proof blocks are ready for
`\leanok`. Per the active prover instructions, the blueprint was left
unchanged for deterministic `sync_leanok`.

## Prior formalization audit

## Assumption/target split

### Governing laws

- `SatisfiesIsotropicPhasePropagation` states the monochromatic radial phase law uniformly for both sources and both observation points: propagation through a path of length `r` subtracts `2π r / λ` from the source phase.
- The predicate also requires the common physical wavelength to have a positive nanometre readout.
- The law is formulated using Physlib's Euclidean `Space 2` distance and the unit-aware wavelength's nanometre readout.

### Previous-part results

- The dataset records no previous parts.
- `source_paths_to_P1_are_equal` and `path_difference_to_P2_in_wavelengths` are new conclusion-side geometry lemmas derived from the figure readouts. They are not assumptions of the target theorem.

### Figure/data readouts

- `HasStatedFigureReadouts` records `λ = 400 nm` and the primary-figure coordinates `S₁ = (0,640) nm`, `S₂ = (0,-640) nm`, `P₁ = (720,0) nm`, and `P₂ = (0,720) nm`.
- `HasStatedPhaseCalibrationAtP1` records only the stated measurement at `P₁`: `S₂` leads `S₁` by `0.600π = 3π/5` radians.
- `answerPhaseDifferenceInWavelengths` faithfully records all four printed choices as exact dimensionless wavelength multiples: `13/5`, `27/10`, `29/10`, and `16/5`.

### Current target conclusion

- `phaseDifferenceAtP2_eq_recordedAnswerC` concludes that the unwrapped phase of `S₁` leads that of `S₂` at `P₂` by `29/10 = 2.90` wavelength cycles, answer C.

## Goal-faithfulness audit

- No premise mentions the arrival-phase difference at `P₂`, answer C, `29/10`, or `2.90`.
- `HasStatedFigureReadouts` contains geometry and wavelength data only; `HasStatedPhaseCalibrationAtP1` concerns `P₁` only.
- `SatisfiesIsotropicPhasePropagation` is a uniform governing law quantified over every source and observation point. It contains no problem-specific target value.
- `phaseLeadRadians` is merely the signed difference of two independently stored arrival phases, and `phaseLeadInWavelengths` merely converts radians to cycles by division by `2π`. Neither helper defines the requested value.
- The answer-choice table records the printed choices but supplies no hypothesis identifying the correct choice.
- The intermediate `16/5` statement is the independently proved geometric path-length difference at `P₂`, not the requested `29/10` phase result. It is not smuggled into the target theorem's premises.
- The orientation is explicit: the given calibration is `S₂` ahead of `S₁` at `P₁`, while the conclusion is `S₁` ahead of `S₂` at `P₂`. This avoids turning an unsigned “phase difference” into an ambiguous absolute-value claim.

## Declarations created and blueprint correspondence

- Physical/unit infrastructure: `DimLength`, `lengthValueIn`, `nanometersValue`.
- Figure labels and physical setup: `SourceLabel`, `ObservationLabel`, `IsotropicPointSource`, `TwoPointSourceSetup`, `xCoordinate`, `yCoordinate`.
- Phase readouts: `phaseLeadRadians`, `phaseLeadInWavelengths`.
- Assumption predicates: `HasStatedFigureReadouts`, `HasStatedPhaseCalibrationAtP1`, `SatisfiesIsotropicPhasePropagation`.
- Answer data: `AnswerChoice`, `answerPhaseDifferenceInWavelengths`.
- Derived geometry: `source_paths_to_P1_are_equal`, `path_difference_to_P2_in_wavelengths`.
- `phaseDifferenceAtP2_eq_recordedAnswerC` corresponds to blueprint label `thm:physics:phyx_mini_0087:target`.

The blueprint chapter already existed and contained `% archon:physics`. It was not edited because the prover write-permission section explicitly protects blueprint chapters; deterministic `sync_leanok` should apply the ready markers.

## LeanExplore queries and candidates actually used

- Natural-language query `physical dimension length SI unit nanometer quantity` found `Dimension`, `Dimension.L𝓭`, `UnitChoices.SI`, and `LengthUnit`.
- Likely-name query `Dimensionful WithDim LengthUnit.nanometers` found and grounded `Dimensionful` and `LengthUnit.nanometers`.
- Natural-language query `Euclidean distance between points in real coordinate space dist` found `Space.dist_eq`, `Space.instDist`, and Mathlib's `EuclideanSpace.dist_eq`; the Physlib `Space` API was selected for its physical interpretation.
- Likely-name query `Space.dist_eq` confirmed the exact Physlib distance declaration and instance.
- Natural-language query `Physlib Space spacetime spatial position coordinates` found `Space`; its source states that `Space d` is flat Euclidean physical space with a chosen length unit and origin.
- Natural-language query `phase angle radians wavelength wave optics` found `ClassicalMechanics.harmonicWave`, `ClassicalMechanics.WaveVector`, and `Real.Angle.toReal`.
- Likely-name query `Real.pi` found and grounded `Real.pi`.

Source/module/docstrings were fetched for the candidates actually evaluated for use: `Dimension`, `Dimension.L𝓭`, `LengthUnit`, `LengthUnit.nanometers`, `Dimensionful`, `Space`, `Space.instDist`, `Space.dist_eq`, `ClassicalMechanics.harmonicWave`, `ClassicalMechanics.WaveVector`, `Real.Angle.toReal`, and `Real.pi`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.nanometers`, `Space`, its function coercion for coordinates, its `Dist` instance, and `Space.dist_eq`.
- Mathlib: `Real.pi` and root `dist` notation through the Physlib `Space` metric instance.

## Local abstractions introduced

- `IsotropicPointSource` keeps a genuine `Space 2` position and an unwrapped emission-phase readout; it is not a scalar alias or one-field scalar wrapper.
- `TwoPointSourceSetup` keeps the common dimensionful wavelength, labeled source/observation geometry, and source- and point-indexed arrival phases distinct.
- `SatisfiesIsotropicPhasePropagation` is the smallest local law interface needed to express spherical isotropic phase propagation by radial path length.
- Unwrapped phases are represented by `ℝ` in radians because the requested `2.90λ` phase difference exceeds one full cycle. `Real.Angle` would quotient modulo `2π` and erase precisely the unwrapped cycle count asked for.

## Grounding gaps

- LeanExplore found `ClassicalMechanics.harmonicWave`, but its phase profile is arbitrary and its surrounding API is aimed at harmonic/plane-wave fields; it does not directly provide a dimensionful-wavelength isotropic point-source propagation law. The local radial phase predicate preserves the required point-source physics without guessing an unavailable API.
- Physlib `Space 2` carries a chosen scalar length unit rather than dimensionful coordinates at the type level. The formalization therefore makes the nanometre chart explicit in `HasStatedFigureReadouts` and connects metric distances to the unit-aware wavelength through `nanometersValue` in the propagation law.
- `.archon/AGENTS.md`, named in the task preamble, was absent from the project. The available `.archon/prover-modes/physics-formalize.md` and `PROGRESS.md` were read and followed.

## Verification

- `archon-lean-lsp` diagnostics: success, no diagnostics.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0087.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, `sorryAx`, local `axiom`, or
  `native_decide`.
- Axiom verification for
  `PhyXMiniProblems.ProblemPhyXMini0087.phaseDifferenceAtP2_eq_recordedAnswerC`:
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Redraft needed

None.
