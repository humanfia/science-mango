# Autoformalization result: `PhyXMiniProblems/problem_phyx_mini_0035.lean`

Archon iteration: 003. The existing revised Lean declaration was audited
against the source report, primary image, and physics blueprint. Its statement
is faithful and required no semantic change; this report is regenerated from
post-formalization searches and verification performed in this iteration.

## Assumption/target split

### Governing laws

- `ObeysThinLensLensmakerEquation setup` states, for every
  `UnitChoices`, the thin-lens lensmaker law in a surrounding medium:
  `1/f = (n_lens/n_medium - 1) * (1/R₁ - 1/R₂)`.
- `UsesLensmakerSignConvention setup` selects the Cartesian branch for
  left-to-right incident light, turning the source's radius magnitudes into
  `R₁ = +9 cm` and `R₂ = -11 cm`.
- `HasPhysicalOpticalParameters setup` states only qualitative positivity
  of the focal length, mirror-radius magnitude, and two refractive indices.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- The primary image confirms the left-to-right order eye, upright object,
  biconvex lens, and concave mirror on one horizontal optical axis. The two
  black points between the lens and mirror and the black point left of the
  lens support retaining the source's labeled axial geometry.
- `MatchesFigureReadouts setup` records the converging lens and concave
  mirror, object--lens separation `8 cm`, lens--mirror separation `20 cm`,
  the two focal-point separations `5 cm`, focal-length readout `5 cm`,
  lens-surface radius magnitudes `9 cm` and `11 cm`, mirror-radius
  magnitude `8 cm`, and surrounding-air index `1`.
- `answerRefractiveIndex` records the displayed dimensionless choices
  A = 1.32, B = 1.44, C = 1.50, and D = 1.99.

### Current target conclusions

- `setup.lensMaterialRefractiveIndex = 199 / 100`.
- The same index equals `answerRefractiveIndex .D`, identifying choice D.

## Goal-faithfulness audit

The requested equality `n = 199/100` is not a field of
`LensMirrorSetup`, `MatchesFigureReadouts`,
`UsesLensmakerSignConvention`, `HasPhysicalOpticalParameters`, or
`ObeysThinLensLensmakerEquation`. The only hypotheses about the unknown
material index are positivity and the general lensmaker equation. The answer
table says what is printed beside D but never assumes that the unknown index
equals D.

Consequently the target still has to be derived from `f = 5`,
`R₁ = 9`, `R₂ = -11`, `n_medium = 1`, and the governing law:
`1/5 = (n - 1) * (1/9 + 1/11)`, hence `n = 199/100`. The mirror radius,
object distance, and lens--mirror spacing remain explicit source data even
though they are distractors for this calculation. No definition unfolds to
make the substantive conclusion true.

## Declarations and blueprint correspondence

- `LengthQuantity`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-lengthquantity`.
- `centimeterUnitChoices`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-centimeterunitchoices`.
- `lengthInCentimeters`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-lengthincentimeters`.
- `FigurePoint`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-figurepoint`.
- `ThinLensKind`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-thinlenskind`.
- `SphericalMirrorKind`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-sphericalmirrorkind`.
- `LensMirrorSetup`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-lensmirrorsetup`.
- `axialSeparationCentimeters`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-axialseparationcentimeters`.
- `MatchesFigureReadouts`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-matchesfigurereadouts`.
- `UsesLensmakerSignConvention`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-useslensmakersignconvention`.
- `HasPhysicalOpticalParameters`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-hasphysicalopticalparameters`.
- `ObeysThinLensLensmakerEquation`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-obeysthinlenslensmakerequation`.
- `AnswerChoice`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-answerchoice`.
- `answerRefractiveIndex`:
  `def:physics:phyx-mini-0035:phyxminiproblems-problemphyxmini0035-answerrefractiveindex`.
- `problem_phyx_mini_0035`:
  `thm:physics:phyx_mini_0035:target`.

No new public helper was added, so no additional blueprint dependency edge is
needed.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `dimensionful physical quantity unit choices length centimeters`
  returned and selected `Dimensionful` (id 394284) and
  `LengthUnit.centimeters` (id 393160); nearby relevant results included
  `UnitChoices.dimScale`, `Dimension`, and
  `CarriesDimension.toDimensionful`.
- Natural-language query
  `thin lens lensmaker equation refractive index radii of curvature`
  returned only unrelated thin-category and Euclidean-sphere declarations,
  including `CategoryTheory.ThinSkeleton` and
  `EuclideanGeometry.Sphere.isIntTangent_iff_dist_center`.
- Natural-language query
  `geometrical optics lens refractive index focal length` returned only
  unrelated reflection, focal-subgroup, inversion, and row-length results.
- Likely-name query
  `Dimensionful WithDim UnitChoices LengthUnit.centimeters` selected
  `LengthUnit.centimeters`, `Dimensionful`, and `Dimension.L𝓭`;
  nearby support results included `HasDim.scaleUnit_apply` and
  `Dimensionful.of_scaleUnit`.
- Exact-name queries `WithDim`, `UnitChoices`, `UnitChoices.SI`, and
  `LengthUnit` selected those declarations and confirmed their related
  APIs.

Source, module, and docstring were fetched after selection for:
`Dimensionful` (394284), `WithDim` (394425), `Dimension.L𝓭` (394324),
`UnitChoices` (394255), `UnitChoices.SI` (394270), `LengthUnit`
(393137), and `LengthUnit.centimeters` (393160).

## Physlib/Mathlib names grounded

- `Dimensionful` and `UnitChoices` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` from `Physlib.Units.Dimension`.
- `UnitChoices.SI` from `Physlib.Units.Basic`.
- `LengthUnit` and `LengthUnit.centimeters` from
  `Physlib.SpaceAndTime.Space.LengthUnit`.
- Mathlib's `ℝ`, order, division, subtraction, and absolute-value
  operations are used for dimensionless indices and scalar readouts.

## Local abstractions introduced

- `FigurePoint` preserves the named points on the common optical axis.
- `ThinLensKind` and `SphericalMirrorKind` preserve the converging and
  concave component roles visible in the source and image.
- `LensMirrorSetup` stores signed unit-aware `Dimensionful` lengths and
  dimensionless refractive indices instead of collapsing physical length to
  `ℝ`.
- `MatchesFigureReadouts`, `UsesLensmakerSignConvention`,
  `HasPhysicalOpticalParameters`, and
  `ObeysThinLensLensmakerEquation` keep source observations, the modeling
  convention, admissibility, and the governing law logically separate.

## Grounding gaps

- No geometrical-optics, thin-lens, spherical-mirror, or lensmaker-law API was
  found in Mathlib/Physlib. The local abstractions above are therefore the
  smallest interfaces that retain the source's physical meaning.
- The optional `archon dag-query` navigation command could not be run because
  `archon` is not installed on this process's `PATH`.

## Redraft requests

- None. The revised Lean statement matches the primary image, source report,
  blueprint, governing law, and recorded answer.
- The blueprint was not edited because this lane's explicit write permissions
  allow only the assigned Lean file and this mirrored result file. A review
  agent may add `\leanok` after accepting the formalization.

## Retry-gate resolution

The iteration-003 gate reason was missing genuine post-formalization evidence.
This report records the actual searches, selected candidates, fetched
source/module/docstrings, grounded names, abstractions, gaps, source/image
readouts, governing-law split, and target-answer audit for the revised Lean
model.

## Verification

- `archon-lean-lsp`: no errors; one expected warning at the theorem body,
  `declaration uses sorry`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0035.lean`: exit code 0;
  the same single expected `sorry` warning.
