# Iteration 003 post-formalization result: `problem_phyx_mini_0041.lean`

## Review-gate resolution

The exact final-review reason is evidence-only: the gate requested a genuine
post-formalization report naming the searches actually run, declarations
actually grounded, local abstractions, gaps, and the source/law/answer split.
The Lean model was therefore preserved. This report was regenerated after
fresh inspection of the current Lean file, blueprint, source JSON, and primary
image; fresh LeanExplore queries; fetched source/module/docstring records; and
fresh LSP plus `lake env lean` verification on 2026-07-23.

## Assumption/target split

### Governing laws

- `ObeysExactSnellLawNearOpticalAxis setup` requires exact Snell refraction for
  every sufficiently near-axis member of the represented surface-ray family.
  It is a neighborhood statement using `∀ᶠ ... in 𝓝 0`, not a globally exact
  paraxial equation.
- `HasFirstOrderSphericalRayGeometry setup` gives the derivatives at zero ray
  height of the incident direction, surface-normal direction, and refracted
  direction. Their coefficients are respectively `1/s`, `-1/R`, and `-1/s'`.
  These state local ray geometry and do not state the Gaussian surface equation.
- `ObeysExactChiefRaySnellLawNearAxis setup` requires exact Snell refraction at
  the surface vertex for all sufficiently small object heights.
- `MapsOpticalAxisToItself setup` fixes the physical zero-height branch.
- `HasLateralMagnificationAtOpticalAxis setup` gives the physical definition of
  lateral magnification as the derivative at zero of image height with respect
  to object height.

### Previous-part results

- None. The source report has `previous_parts: []`.
- The image-distance equality `s' = -64/3 cm` is deliberately a proved
  intermediate lemma, not a previous-part premise.

### Figure/data readouts

- `HasStatedRefractiveIndices setup` records the prose labels
  `n_water = 1.33` and `n_glass = 1.52`.
- `MatchesFigureReadout setup` records `s = 8.00 cm`, `R = 2.00 cm`, the center
  one radius into the glass, and the raster ordering
  `PPrime < P < vertex < C`.
- `HasPhysicalSigns setup` records positivity of both refractive indices, the
  object distance, and the radius.
- The figure supplies no numerical value for `s'` or the magnification.

### Current target conclusions

- `signedImageDistanceCentimeters_eq_neg_sixty_four_thirds`: the paraxial
  signed image distance is `-64/3 cm`.
- `problem_phyx_mini_0041`: the lateral magnification is exactly `7/3` and this
  exact value is within the displayed rounding tolerance of answer B, `+2.33`.

## Goal-faithfulness audit

The numerical image distance, magnification `7/3`, and answer choice B do not
occur in any setup field, governing-law predicate, figure predicate, or local
definition. `CylindricalGlassRodSetup.lateralMagnification` is independent
data; `HasLateralMagnificationAtOpticalAxis` constrains only its physical role
as a derivative and gives no numerical value. Likewise, `PPrime` is independent
dimensionful axial data, and `HasFirstOrderSphericalRayGeometry` identifies its
signed distance only as the first-order axis intercept through the coefficient
`-1/s'`; it does not state the Gaussian relation or its numerical solution.

The prior draft's global equalities
`n_a/s + n_b/s' = (n_b-n_a)/R` and
`m = -n_a*s'/(n_b*s)` were removed from the premises. In the redraft these are
consequences to be obtained by differentiating exact local Snell laws. This
directly addresses the review gate's globalized-approximation blocker.

## Declarations and blueprint labels

- `problem_phyx_mini_0041` corresponds to
  `thm:physics:phyx_mini_0041:target`.
- `signedImageDistanceCentimeters_eq_neg_sixty_four_thirds` corresponds to
  `lem:physics:phyx-mini-0041:phyxminiproblems-problemphyxmini0041-signedimagedistancecentimeters-eq-neg-sixty-four-thirds`.
- Every helper is pinned in the chapter. With common prefix
  `def:physics:phyx-mini-0041:phyxminiproblems-problemphyxmini0041-`, the
  declaration-to-label suffixes are:

| Lean declaration | Blueprint label suffix |
|---|---|
| `DimLength` | `dimlength` |
| `centimeterUnitChoices` | `centimeterunitchoices` |
| `lengthInCentimeters` | `lengthincentimeters` |
| `OpticalMedium` | `opticalmedium` |
| `FigurePoint` | `figurepoint` |
| `CylindricalGlassRodSetup` | `cylindricalglassrodsetup` |
| `axialCoordinateCentimeters` | `axialcoordinatecentimeters` |
| `objectDistanceCentimeters` | `objectdistancecentimeters` |
| `signedImageDistanceCentimeters` | `signedimagedistancecentimeters` |
| `signedRadiusCentimeters` | `signedradiuscentimeters` |
| `HasStatedRefractiveIndices` | `hasstatedrefractiveindices` |
| `HasPhysicalSigns` | `hasphysicalsigns` |
| `MatchesFigureReadout` | `matchesfigurereadout` |
| `ObeysExactSnellLawNearOpticalAxis` | `obeysexactsnelllawnearopticalaxis` |
| `HasFirstOrderSphericalRayGeometry` | `hasfirstordersphericalraygeometry` |
| `chiefRayIncidentAngleRadians` | `chiefrayincidentangleradians` |
| `chiefRayRefractedAngleRadians` | `chiefrayrefractedangleradians` |
| `MapsOpticalAxisToItself` | `mapsopticalaxistoitself` |
| `ObeysExactChiefRaySnellLawNearAxis` | `obeysexactchiefraysnelllawnearaxis` |
| `HasLateralMagnificationAtOpticalAxis` | `haslateralmagnificationatopticalaxis` |
| `AnswerChoice` | `answerchoice` |
| `AnswerChoice.magnificationReadout` | `answerchoice-magnificationreadout` |
| `AnswerChoice.displayTolerance` | `answerchoice-displaytolerance` |
| `MatchesAnswerChoice` | `matchesanswerchoice` |

These declarations preserve the dimensional, figure, local-ray, and
multiple-choice roles needed by the target. The chapter was not edited to add
`\leanok`: the task's explicit write-permission list permits edits only to the
assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Query: `spherical refracting surface Gaussian equation lateral magnification optics`.
  Returned only unrelated spherical-coordinate and probability-Gaussian
  declarations; no optics API was usable.
- Query: `Snell law geometric optics refraction refractive index`.
  Returned `EuclideanGeometry.law_sin` and unrelated polynomial/geometric
  declarations; no Snell-refraction API was usable.
- Query: `HasDerivAt first order linear approximation derivative at a point`.
  Used candidate `HasDerivAt` (id `124761`). Its fetched source confirms the
  local expansion `f x' = f x + (x' - x) • f' + o(x' - x)`.
- Query: `Dimensionful WithDim physical length UnitChoices`.
  Used candidates `Dimensionful` (id `394284`) and `Dimension.L𝓭`
  (id `394324`).
- Query: `WithDim`.
  Used candidate `WithDim` (id `394425`).
- Query: `WithDim UnitChoices UnitChoices.SI`.
  Used candidate `UnitChoices.SI` (id `394270`).
- Query: `LengthUnit.centimeters`.
  Used candidate `LengthUnit.centimeters` (id `393160`).
- Query: `Real.arctan derivative`.
  Used `Real.hasDerivAt_arctan'` (id `146692`) to ground the chosen exact
  chief-ray angle representation with `Real.arctan`.
- Query: `Real.sin derivative`.
  Used `Real.hasDerivAt_sin` (id `147274`) to ground differentiation of the
  exact Snell relations.

Source, module, and docstring fields were fetched for the intended candidates
`HasDerivAt`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices.SI`,
`LengthUnit.centimeters`, `Real.hasDerivAt_sin`, and
`Real.hasDerivAt_arctan'`. The two derivative theorems have null docstrings,
but their fetched sources and modules confirm their signatures.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`,
  `UnitChoices.SI`, and `LengthUnit.centimeters`.
- Mathlib: `HasDerivAt`, `Real.sin`, `Real.arctan`, neighborhood notation `𝓝`,
  and filter-eventual notation `∀ᶠ`.
- Future proofs are grounded by the fetched derivative declarations
  `Real.hasDerivAt_sin` and `Real.hasDerivAt_arctan'`.

## Local abstractions introduced

No Mathlib/Physlib spherical-refraction or Snell-law declaration was found.
The file therefore introduces the smallest local interface that retains the
missing physics:

- three angle profiles indexed by surface ray height;
- an image-height map indexed by small object height;
- exact Snell-law predicates local to the optical axis;
- a `HasDerivAt` structure for first-order spherical geometry; and
- a `HasDerivAt` predicate defining lateral magnification.

The abstractions retain radians as dimensionless scalar readouts, centimeter
arguments as explicitly named scalar projections, and all axial positions and
the physical radius as Physlib `Dimensionful` lengths. Allowing independent
angle profiles means finite-height rays may exhibit spherical aberration; only
their behavior at the axis is constrained to define the paraxial image.

## Source/law/answer audit

- Primary image `phyx_data/test_image/41.png` was inspected. It shows water on
  the left, glass on the right, `P'` left of `P`, `P` left of the hemispherical
  vertex, and `C` in the glass. It labels `s = 8.00 cm`, `n_a = 1.33`, and
  `n_b = 1.52`.
- The prose supplies `R = 2.00 cm`; the figure geometry fixes its positive sign
  toward `C` in the glass.
- Differentiating the exact local Snell law gives
  `n_a/s + n_b/s' = (n_b-n_a)/R`, hence `s' = -64/3 cm` for the source data.
- Differentiating the exact chief-ray Snell law gives
  `m = -n_a*s'/(n_b*s) = 7/3`. This differs from `2.33` by `1/300`, within the
  half-unit-last-place tolerance `1/200`, so recorded answer B is consistent.

## Grounding gaps and redraft requests

- Grounding gap: LeanExplore exposed no Mathlib/Physlib API for refractive
  indices, Snell refraction, spherical refracting surfaces, or paraxial lateral
  magnification. The local abstractions above are therefore necessary.
- `.archon/AGENTS.md` was absent in this project checkout. The available
  `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- The `archon` executable advertised for DAG navigation was not available in
  this shell. The chapter's local `\lean`/`\uses` topology was inspected
  directly instead.
- Redraft request: none for the Lean statement. A blueprint-authorized agent
  should add `\leanok`; this agent was explicitly forbidden to edit the
  chapter.

## Verification

- `archon-lean-lsp` diagnostics: success; only the two expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0041.lean`: exit code `0`;
  only the same two expected `sorry` warnings.
