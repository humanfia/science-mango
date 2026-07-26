## Assumption/target split

### Governing laws

- `SatisfiesPupilAcuityTrend` states only the qualitative source law: below the normal `3 mm` optimum, diffraction dominates; above it, aberration dominates.
- `SatisfiesRayleighCriterion` states the circular-aperture law `alpha = 1.22 * wavelength / pupilDiameter` in every `LengthUnit`. It does not assign a wavelength.
- `SatisfiesControlledFigureGeometry` separates exact centered geometry from its approximation. Its first conjunct states `d / s = 2 * tan (alpha / 2)` through unit readouts. Its second conjunct is a local, uniform cubic remainder contract on `|theta| <= paraxialValidityRadiusRad` for replacing `2 * tan (theta / 2)` by `theta`.
- `UsesControlledRayleighRegime` records that these diffraction and locally controlled geometric laws are the intended model.
- `HasPhysicalParameters` supplies positivity, a positive local validity radius, membership of the actual angle in that radius, avoidance of the tangent singularity, and a nonnegative remainder coefficient.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts and metadata

- `FigureLengthLabel.d` and `.s`, together with `FigureAngleLabel.alpha`, preserve the three labels visible in `phyx_data/test_image/75.png`. `figureLength` and `figureAngleRad` attach them to the modeled diameter, axial chart distance, and angular separation.
- `MatchesProblemReadouts` contains only source data: pupil diameter `2.0 mm`, normal optimum `3 mm`, chart distance `20 ft`, and bright lighting.
- `SourceLeavesWavelengthUnspecified` explicitly records that the source gives visible-light context but no numerical illumination wavelength.
- `AnswerChoice`, `displayedDiameterInMillimeters`, and `recordedDatasetAnswer = .C` retain the printed choices and dataset answer as metadata only.

### Current target conclusions

For the arbitrary positive physical wavelength in `setup`, `problem_phyx_mini_0075` concludes:

- the source-specified `2 mm` pupil is in the diffraction-dominated regime;
- the minimum resolved diameter in millimeters is the symbolic exact-geometry expression
  `s * (2 * tan (theta / 2))`, where `theta = 1.22 * wavelength / pupilDiameter`;
- the difference from the paraxial diameter `s * theta` obeys the locally supplied cubic error bound.

It deliberately concludes neither a numerical diameter nor a nearest answer choice, because both are wavelength-sensitive and the source supplies no wavelength.

## Goal-faithfulness audit

The setup stores an unknown dimensionful `minimumResolvedCircleDiameter`; no field assigns it a value or an answer label. The Rayleigh hypothesis relates only `alpha`, wavelength, and pupil diameter. The geometry hypothesis relates `d`, `s`, and `alpha` and supplies a uniform local remainder law before any Rayleigh substitution. Neither premise contains the theorem's combined wavelength-parametric diameter formula.

No `550 nm` readout occurs anywhere. The recorded answer C is not used in the theorem and is not asserted to be correct or closest. The target is therefore derived from distinct source readouts and governing laws rather than reproduced in a premise or made true by unfolding a definition.

## Source/law/answer audit

- Source-supported numeric data: `2 mm`, `3 mm`, `20 ft`, bright light, and the four displayed choices.
- Figure evidence inspected directly: `d` at the chart, axial `s`, and full angular separation `alpha` between the limiting rays.
- Modeling laws: Rayleigh's `1.22 * lambda / D` criterion and exact symmetric tangent geometry, with an explicit local cubic paraxial contract.
- Unsupported datum removed: the prior conventional `550 nm` wavelength.
- Recorded answer treatment: C remains metadata only; no numerical correctness claim is formalized.

## Declarations and blueprint mapping

- Main declaration: `problem_phyx_mini_0075` corresponds to `thm:physics:phyx_mini_0075:target`.
- Existing pinned roles retained under their current names: `LengthQuantity`, `lengthReadout`, `lengthInMillimeters`, `lengthInFeet`, `FigureLengthLabel`, `FigureAngleLabel`, `LightingCondition`, `AcuityLimitation`, `ResolutionRegime`, `EyeChartResolutionSetup`, `figureLength`, `figureAngleRad`, `HasPhysicalParameters`, `MatchesProblemReadouts`, `SatisfiesPupilAcuityTrend`, `SatisfiesRayleighCriterion`, `AnswerChoice`, `displayedDiameterInMillimeters`, `recordedDatasetAnswer`, and `dominantLimitation_eq_diffraction`.
- New redraft helpers: `centralAngleDiameterRatio` depends directly on `Real.tan`; `paraxialAngularRemainder` depends on `centralAngleDiameterRatio`.
- Renamed/replaced abstractions: `WavelengthModel` became `WavelengthProvenance`; `UsesRepresentativeVisibleWavelength` became `SourceLeavesWavelengthUnspecified`; `UsesRayleighParaxialRegime` became `UsesControlledRayleighRegime`; `SatisfiesParaxialFigureGeometry` became `SatisfiesControlledFigureGeometry` and now depends directly on `figureLength`, `figureAngleRad`, `centralAngleDiameterRatio`, and `paraxialAngularRemainder`.
- Removed as unsupported or isolated: unused `lengthInMeters`, `lengthInNanometers`, the hard-coded representative-wavelength predicate, `displayedChoiceError`, `IsClosestDisplayedChoice`, and `IsUniqueClosestDisplayedChoice`.

The chapter's generated declaration topology still describes the rejected pre-redraft model. Write permissions prohibited editing the blueprint chapter, so an authorized blueprint synchronization step should regenerate these pins/edges and add `\leanok` after accepting the revised declaration.

## LeanExplore queries and candidates actually used

All supported searches used `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical length quantities unit choices LengthUnit meters millimeters` found and motivated use of `Dimensionful` (id 394284), `UnitChoices` (394255), `LengthUnit` (393137), `Dimension.L𝓭` (394324), and the unit-scaling infrastructure.
- `WithDim` and `WithDim dimension tagged real quantity` grounded `WithDim` (394425) from `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` grounded the Physlib length dimension (394324).
- `LengthUnit.millimeters LengthUnit.feet LengthUnit.meters` and exact follow-up `LengthUnit.feet` grounded `LengthUnit.millimeters` (393159) and `LengthUnit.feet` (393163). Meter availability and all names were also checked by elaborating the real file.
- `Real.tan` grounded Mathlib's real tangent function (128821), used by `centralAngleDiameterRatio`.
- `paraxial small angle tangent Taylor remainder bound local approximation` returned general candidates such as `taylor_mean_remainder_lagrange` (127692), `AnalyticAt.exists_eq_sum_add_pow_mul` (120668), and `Real.sin_bound` (129029). They were not used in this statement-only formalization; a concrete local cubic contract is clearer and physics-specific.
- `HasDerivAt tan derivative at zero Taylor remainder` and `paraxial optics small-angle approximation` found general calculus/asymptotics support such as `HasFDerivAt.isLittleO` (126269), but no ready-made paraxial optics law.
- `Rayleigh diffraction criterion circular aperture angular resolution` found only unrelated Rayleigh-quotient and generic angular declarations, not the optical Rayleigh criterion.

Source/module/docstring details were fetched for the candidates actually used: `Dimensionful`, `UnitChoices`, `LengthUnit`, `WithDim`, `Dimension.L𝓭`, `LengthUnit.millimeters`, `LengthUnit.feet`, and `Real.tan`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.millimeters`, and `LengthUnit.feet`.
- Mathlib: `Real.tan`, `Real.pi`, real absolute value notation, and real powers.

## Local abstractions introduced

- `WavelengthProvenance` distinguishes an unspecified source wavelength from later measured or monochromatically specified values without collapsing wavelength to a scalar placeholder.
- `EyeChartResolutionSetup` keeps wavelengths and all distances as Physlib dimensionful length quantities; only radian readings and dimensionless remainder controls are real scalars.
- `centralAngleDiameterRatio` faithfully captures the exact centered geometry visible in the figure.
- `paraxialAngularRemainder` and `SatisfiesControlledFigureGeometry` replace the rejected exact global small-angle approximation by an explicit local error contract.
- `SatisfiesRayleighCriterion` is local because no optical Rayleigh-criterion declaration was found in Mathlib/Physlib.

## Grounding gaps and redraft requests

- Mathlib/Physlib provide no circular-aperture Rayleigh resolution law or packaged paraxial eye-chart model; the two physics predicates above are therefore necessary local abstractions.
- The source does not provide a wavelength or an approximation tolerance, so no numerical answer choice is source-grounded. A later theorem may specialize this symbolic result only after adding an independently justified wavelength and a concrete remainder bound.
- `archon dag-query` was unavailable in the runtime (`archon: command not found`), so no dependency-graph result was used.
- The blueprint topology and `\leanok` markers require an authorized resync because this prover was expressly limited to the assigned Lean file and this task-result file.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0075.lean` exits successfully.
After proof completion, its only diagnostics are unused-variable warnings for
the frozen `h_wavelengthSource` and `h_regime` hypotheses.

# Iteration 014 prover result

## Status

Lean proof complete. Both declarations are proved without changing any
declaration header:

- `dominantLimitation_eq_diffraction`;
- `problem_phyx_mini_0075`.

There are no remaining `sorry`, `admit`, `native_decide`, or added `axiom`
occurrences in the assigned Lean file.

## Proof summary

- The pupil-acuity trend is specialized to the stated `2 mm < 3 mm` readouts,
  yielding diffraction as the dominant limitation.
- The Rayleigh law is specialized to millimeters to identify the modeled
  angular separation with `theta`.
- Exact centered geometry gives the symbolic resolved diameter.
- The local cubic paraxial remainder bound is instantiated at `theta` and
  scaled by the strictly positive millimeter readout of the chart distance.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0075.lean` succeeded.
- Lean LSP diagnostics contain no errors. The two warnings are only for the
  frozen provenance and regime hypotheses not being needed by the symbolic
  conclusion.
- `lean_verify` reports no suspicious source patterns. The target theorem uses
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Prior review blocker

The iteration-013 review marked this target `partial` despite confirming that
the proof compiles and is sound. Its sole blocker is the protected blueprint
contract:

- Review record:
  `.archon/logs/iter-013/review-targets/PhyXMiniProblems_problem_phyx_mini_0075/attempt-1/summary.md`.
- Original problem: `phyx_mini_0075`.
- Source report: `reports/phyx_mini/problem_phyx_mini_0075.source.json`.
- The blueprint theorem block still lists the superseded representative
  wavelength, global paraxial equality, and unique closest-choice-C
  dependencies.
- The frozen Lean theorem instead faithfully reflects the missing source
  wavelength by proving a symbolic exact-geometry formula plus a controlled
  paraxial error bound.

An authorized blueprint synchronization pass should replace the stale theorem
dependencies with `SourceLeavesWavelengthUnspecified`,
`UsesControlledRayleighRegime`, `centralAngleDiameterRatio`,
`paraxialAngularRemainder`, and `SatisfiesControlledFigureGeometry`, then add
the corresponding `\leanok` markers. This prover did not edit the blueprint
because its write permissions explicitly allow only the assigned Lean file and
this task-result file.

## Redraft needed

No Lean statement redraft is needed, and no proof blocker remains. Only the
authorized blueprint synchronization described above is outstanding.

# Iteration 015 prover result

## Status

The assigned Lean file was already proof-complete at the iteration-015
baseline, so no proof-body change was necessary. The frozen signatures of both
proved declarations remain unchanged:

- `dominantLimitation_eq_diffraction`;
- `problem_phyx_mini_0075`.

There are no remaining `sorry`, `admit`, `sorryAx`, `native_decide`, or added
`axiom` occurrences in the assigned Lean file.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0075.lean` exits
  successfully.
- Lean LSP diagnostics report no errors. The only diagnostics are unused-variable
  warnings for the frozen `h_wavelengthSource` and `h_regime` hypotheses.
- `lean_verify` reports no suspicious source patterns for either proved
  declaration. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
- The assigned Lean file is byte-for-byte identical to
  `.archon/logs/iter-015/snapshots/PhyXMiniProblems_problem_phyx_mini_0075/baseline.lean`.

## Mandatory proof-review retry

The iteration-013 and iteration-014 proof reviews both confirm that the Lean
proof compiles, is sound, preserves the frozen signature, and correctly
combines the pupil trend, Rayleigh law, exact tangent geometry, and local cubic
error bound. Both reviews remain `partial` solely because the blueprint theorem
block still names the superseded representative-wavelength, global-paraxial,
and unique-closest-choice-C contract.

This prover's write permissions allow changes only to the assigned Lean file
and this task-result file, and explicitly prohibit editing the blueprint
chapter. Consequently, the review blocker cannot be repaired in this lane.
An authorized blueprint synchronization pass must update
`blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0075.tex` to the
current symbolic exact-geometry contract and add the applicable `\leanok`
markers.

## Redraft needed

No Lean statement redraft and no proof repair are needed. The only outstanding
blocker is the protected blueprint synchronization described above.
