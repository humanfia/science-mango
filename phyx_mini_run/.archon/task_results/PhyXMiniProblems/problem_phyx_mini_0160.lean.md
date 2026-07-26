# Autoformalization result: `problem_phyx_mini_0160.lean`

## Assumption/target split

### Governing laws

- `SatisfiesParaxialSphericalMirrorLaws.mirror_equation` states the signed paraxial mirror equation `1/p + 1/q = 1/f` for every length unit and every positive, nonfocal object distance.
- `SatisfiesParaxialSphericalMirrorLaws.lateral_magnification_law` states the signed lateral-magnification law `m = -q/p`, again in every length unit.
- `HasPhysicalParameters` records only positivity and the fact that the requested object distance is not the focal distance.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemAndGraph` records a concave spherical mirror, the horizontal `p (cm)` axis, the vertical dimensionless `m` axis, `p_a = 2 cm`, `p_b = 8 cm`, the requested `p = 14 cm`, and the positive/increasing displayed branch.
- `HasFigureDerivedFocalCalibration` records the intermediate `f = 10 cm` calibration obtained by fitting the intended magnification graph to the spherical-mirror model. It does not state the magnification at `14 cm`.
- `AnswerChoice.displayedMagnification` records choices A through D, and `recordedDatasetAnswer` records D.

### Current target conclusions

- `requestedSignedImageDistanceCentimeters_eq_thirty_five`: the derived signed image distance at the requested object position is `q = 35 cm`.
- `problem_phyx_mini_0160`: the derived lateral magnification at `p = 14 cm` is exactly `-5/2`, and hence agrees with displayed choice D.

## Goal-faithfulness audit

- No hypothesis, setup field, law field, or validity predicate states `m(14 cm) = -5/2` or selects choice D as a physical premise.
- `lateralMagnificationAt` is an unconstrained response function until the general mirror and magnification laws are supplied.
- The `10 cm` focal calibration is a distinct intermediate figure-derived optical quantity. Together with the general laws and the independent `14 cm` object-distance readout it entails, but is not definitionally equal to, the requested magnification.
- `MatchesDisplayedAnswer` is used only on the conclusion side. Unfolding it does not produce evidence for the answer without first deriving the magnification.
- Lengths are not bare scalar aliases: they use Physlib's unit-dependent `Dimensionful (WithDim L𝓭 ℝ)`. Real numbers occur only as signed unit readouts or dimensionless magnifications.

## Declarations and blueprint labels

- Local physical/unit model: `LengthQuantity`, `lengthReadout`, `lengthInCentimeters`.
- Geometry and figure labels: `SphericalMirrorKind`, `GraphVariable`.
- Setup and assumptions: `SphericalMirrorMagnificationSetup`, `MatchesProblemAndGraph`, `HasFigureDerivedFocalCalibration`, `HasPhysicalParameters`, `IsFiniteObjectConfiguration`, `SatisfiesParaxialSphericalMirrorLaws`.
- Answer data: `AnswerChoice`, `AnswerChoice.displayedMagnification`, `recordedDatasetAnswer`, `MatchesDisplayedAnswer`.
- Intermediate lemma: `requestedSignedImageDistanceCentimeters_eq_thirty_five`.
- Blueprint label `thm:physics:phyx_mini_0160:target` corresponds to `problem_phyx_mini_0160`.
- The target theorem is ready for the blueprint statement's `\leanok` marker. The blueprint was not edited because prover write permissions explicitly restrict edits to the assigned Lean file and this result file.

## LeanExplore queries/candidates actually used

- Query `spherical mirror equation object distance image distance focal length lateral magnification`: no matching geometrical-optics API; `LengthUnit` was the only physically relevant result. Sphere-geometry and polynomial-mirror hits were incompatible.
- Query `geometrical optics thin lens mirror magnification`: no compatible optics law was returned.
- Queries `physical dimensions length quantity SI centimetre` and `Unitful length centimetre quantity`: selected `LengthUnit`, `LengthUnit.centimeters`, `UnitChoices.SI`, and the Physlib dimensional framework.
- Queries `Dimensionful WithDim L𝓭 physical length scalar value in selected units`, `toDimensionful WithDim CarriesDimension`, and `Dimensionful add divide physical quantity`: selected `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and the function-like unit readout for `Dimensionful` quantities.
- Source/module/docstrings were fetched for `LengthUnit`, `LengthUnit.centimeters`, `UnitChoices.SI`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `CarriesDimension.toDimensionful`, and the `Dimensionful` coercion. Only the names needed by the file were imported/used.

## Grounded Mathlib/Physlib names

- `Dimensionful`
- `WithDim`
- `Dimension.L𝓭`
- `UnitChoices`
- `UnitChoices.SI`
- `LengthUnit`
- `LengthUnit.centimeters`

## Local abstractions introduced

- Physlib/Mathlib has no spherical-mirror equation or lateral-magnification API in the LeanExplore results. `SphericalMirrorMagnificationSetup` and `SatisfiesParaxialSphericalMirrorLaws` therefore provide the smallest local interface retaining the mirror kind, focal length, signed image-distance response, magnification response, sign convention, and the two governing laws.
- `GraphVariable` and `MatchesProblemAndGraph` preserve the graph labels, domain endpoints, and qualitative curve behavior without treating those labels as unrelated scalar placeholders.

## Grounding gaps and redraft requests

- The supplied file `phyx_data/test_image/160.png` is not the graph described by the chapter/source report. It depicts a converging thin lens with ray traces and a virtual image. The chapter describes a spherical-mirror `m`-versus-`p` graph. The source image should be corrected or the chapter should be redrafted to match it.
- Because the intended graph is unavailable, its raw numerical curve point cannot be verified. The formalization makes the necessary intermediate graph-fit calibration `f = 10 cm` explicit rather than hiding it in the laws or target. The plan/review agent should replace this with a verified raw graph readout if the correct figure is recovered.
- The chapter contains the generic autoformalization instruction but no problem-specific informal derivation. A redraft should explicitly state how the graph yields `f = 10 cm`, followed by `q = 35 cm` and `m = -5/2`.
- The requested `archon dag-query` navigation command was unavailable in this runtime (`archon: command not found`), so no dependency-graph declaration was used.

## Verification

- `archon-lean-lsp` reported exactly two expected `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0160.lean` exited successfully with the same two expected warnings.
