# Autoformalization result: `problem_phyx_mini_0133.lean`

## Assumption/target split

### Governing laws

- `UsesSurfaceToCenterLensmakerConvention` fixes the physical sign convention: each Cartesian lensmaker radius is the directed displacement from its surface vertex to its curvature centre. It also relates the differently oriented radius annotations in the image to those physical radii.
- `ObeysThinLensLensmakerEquation` states the paraxial thin-lens law in every `UnitChoices` system:
  `1/f = (n_glass/n_air - 1) * (1/R₁ - 1/R₂)`.
- `HasPhysicalOpticalParameters` supplies only positivity/nonzero conditions needed for a physical and algebraically nondegenerate optical model.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `MatchesProblemDescription` records glass index `1.50`, air index `1`, the convex-meniscus description, the auxiliary caption's conflicting word `biconcave`, and the required image-primary evidence policy.
- `MatchesPrimaryFigure` records the left convex and right concave surfaces, points `C₁` and `C₂`, their axial ordering, vertex-to-centre radius magnitudes `22 cm` and `46 cm`, and the printed signed annotations `R₁ = 22 cm` and `R₂ = -46 cm`.
- The four displayed answer values are stored by `answerFocalLengthMeters`; `recordedAnswerChoice = .C` is metadata and is not a theorem premise.

### Current target conclusions

- The physical focal-length metre readout is exactly `253 / 300`.
- That exact value agrees to the nearest hundredth of a metre with answer choice C, `0.84 m`.

## Goal-faithfulness audit

The focal-length value `253/300` and the predicate selecting choice C occur only in the conclusion of `problem_phyx_mini_0133`. No premise structure contains either conclusion, and `focalLength` remains an unconstrained dimensionful field except for nonzeroness and the governing lensmaker equation. `MatchesAnswerToNearestHundredthMeter` is only a comparison against the printed options; it is not assumed.

The image's `R₂ = -46 cm` annotation was not silently fed into the standard Cartesian lensmaker formula. The file distinguishes the left-pointing figure annotation from the physical surface-to-centre radius. Since both depicted centres lie to the right of their vertices, the lensmaker radii derived from the geometry are `+22 cm` and `+46 cm`; the second annotation has the reverse orientation. This gives the exact physical result `253/300 m`, which rounds to the recorded `0.84 m`.

The auxiliary caption calls the lens biconcave, while the problem prose and primary image show a convex meniscus. Both reports are retained in separate fields and `imagePrimary` selects the primary visual evidence, so the discrepancy is explicit rather than erased.

## Declarations and blueprint correspondence

- `OpticalLength`, `lengthReadout`, `lengthInMeters`, `lengthInCentimeters`: dimensionful length model and scalar unit readouts.
- `LensSurface`, `SurfaceShape`, `FigurePoint`, `OpticalMedium`, `LensDescription`, `OpticalApproximation`, `FigureEvidencePolicy`: physical and figure labels.
- `MeniscusLensSetup`: the physical lens, refractive indices, focal length, two notions of signed radius, axial geometry, and source metadata.
- `MatchesProblemDescription`, `MatchesPrimaryFigure`: problem and figure data.
- `UsesSurfaceToCenterLensmakerConvention`, `HasPhysicalOpticalParameters`, `ObeysThinLensLensmakerEquation`: geometry/sign, physical, and governing-law assumptions.
- `lensmaker_radius_readouts_from_figure`: helper lemma deriving the two Cartesian radius readouts from the primary figure and sign convention.
- `AnswerChoice`, `answerFocalLengthMeters`, `recordedAnswerChoice`, `MatchesAnswerToNearestHundredthMeter`: multiple-choice metadata and explicit rounding criterion.
- `problem_phyx_mini_0133`: formalizes `thm:physics:phyx_mini_0133:target`.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `thin lens lensmaker equation radius of curvature refractive index focal length`: no lensmaker or thin-lens law was returned. `LengthUnit` was the only relevant unit candidate.
- Likely-name query `Lensmaker`: returned no optics candidate.
- Query `Dimensionful WithDim length LengthUnit centimeters`: selected `Dimensionful` (id 394284), `LengthUnit.centimeters` (id 393160), and `Dimension.L𝓭` (id 394324). Source, module, and docstring were fetched for all three.
- Likely-name query `WithDim`: selected `WithDim` (id 394425); source, module, and docstring were fetched.
- Likely-name query `UnitChoices`: selected `UnitChoices` (id 394255) and `UnitChoices.SI` (id 394270); source, module, and docstring were fetched.
- Queries `LengthUnit.meters` and `the base SI length unit meter`: the former did not return the exact declaration, while the fetched source of `UnitChoices.SI` directly confirmed its use of `LengthUnit.meters`.
- Query `nearest decimal rounding real number`: found Mathlib's `round` (id 99909), but it was not used. A half-unit-in-the-last-place inequality is clearer for the answer's two-decimal precision and needs no additional rounding API.

## PhysLean/Mathlib names grounded

- `Dimensionful` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` from `Physlib.Units.Dimension`.
- `LengthUnit.centimeters` from `Physlib.SpaceAndTime.Space.LengthUnit`.
- `UnitChoices` and `UnitChoices.SI` from `Physlib.Units.Basic`; the latter grounds `LengthUnit.meters`.

The assigned file imports `Physlib.Units.WithDim.Basic`, which transitively supplies these unit and dimension declarations.

## Local abstractions introduced

- No matching Mathlib/Physlib lensmaker declaration was found, so `ObeysThinLensLensmakerEquation` is a local governing-law interface. It preserves the refractive-index ratio, both signed dimensionful radii, the focal length, the paraxial approximation, and unit covariance.
- The figure-label enums and `MeniscusLensSetup` are minimal local abstractions for the two surfaces, their vertices and curvature centres, the two media, the conflicting source descriptions, and the dimensionful optical quantities.
- `MatchesAnswerToNearestHundredthMeter` uses the physically stated metre readout and a `0.005 m` tolerance, exactly half the final printed decimal place.

## Grounding gaps

- LeanExplore exposed no ready-made Mathlib/Physlib thin-lens or lensmaker equation, so the faithful local law above is required.
- The expected `.archon/AGENTS.md` role file was absent. The available `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- The assigned Lean file did not yet exist, so it was created; consequently there were no file-specific `/- USER: ... -/` comments to apply.
- The blueprint chapter exists, but it was not edited to add `\leanok` because the explicit write permissions allow changes only to the assigned Lean file and this task-result file. The coordinating agent should add `\leanok` to `thm:physics:phyx_mini_0133:target`.

## Verification

- `archon-lean-lsp` diagnostics report no errors and exactly two expected `declaration uses sorry` warnings, for the helper lemma and target theorem.
