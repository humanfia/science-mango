# Autoformalization result: `problem_phyx_mini_0050.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSnellLawAtPrismFaces` states Snell's law independently at the
  entry and exit faces, using angles measured from each face's forward normal.
  It contains no numerical value for the prism index.
- `HasPhysicalRefractiveIndices` states the idealized air-index readout `1`
  and positivity of the air and prism indices. It does not constrain the prism
  index to the requested answer or to the final sine quotient.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the theorem
  assumes no prior computed result.

### Figure/data readouts

- `MatchesFigureReadouts` records the `30°-60°-90°` prism data, the incident
  horizontal direction, and the pictured `22.6°` downward deflection.
- `HasDepictedPrismGeometry` records the triangle-angle sum, the horizontal
  entry normal, and the exit normal determined by the top `30°` geometry.
- `HasDepictedRayPath` records normal-incidence propagation through the entry
  face and the clockwise outgoing deflection.
- `answerRefractiveIndex` transcribes all four displayed dimensionless answer
  readouts: A `0.64`, B `1.59`, C `0.89`, and D `1.24`.

### Current target conclusions

- `exit_interface_angles_from_figure` derives, rather than assumes, the exit
  incidence angle `30°` and refraction angle `52.6°`.
- `prism_refractive_index_exact_formula` derives the prism-index readout
  `sin(52.6°) / sin(30°)` from the figure geometry, air idealization, and
  Snell's law.
- `problem_phyx_mini_0050` concludes both that exact symbolic expression and
  agreement to the nearest hundredth with answer choice B (`1.59`).

## Goal-faithfulness audit

The requested prism index, the sine quotient, and the conclusion that choice B
matches occur only in lemma/theorem conclusions. They do not occur in
`PrismLaserSetup`, `MatchesFigureReadouts`, `HasDepictedPrismGeometry`,
`HasDepictedRayPath`, `HasPhysicalRefractiveIndices`, or
`SatisfiesSnellLawAtPrismFaces`. In particular, the Snell-law predicate is the
general interface law at each crossed face, not the solved formula for this
problem.

`angleFromPropagationNormal` is a generic absolute direction difference, and
`MatchesAnswerToNearestHundredth` is a generic rounding predicate. Neither
definition selects B by unfolding. The substantive angle, exact-index, and
rounding claims all remain `by sorry` proof obligations, as required at the
autoformalize stage.

The refractive index is represented as Physlib's unit-independent
`Dimensionful (WithDim (1 : Dimension) ℝ)`, not as a transparent scalar alias
or a local one-field physical wrapper. `dimensionlessReadout` is an explicitly
named scalar projection used where trigonometric laws and displayed answers
need real values. Degree labels, radian direction readouts, and answer values
are real numbers because they are dimensionless measured scalars.

## Declarations created and blueprint labels

- Physlib quantity/readout layer: `DimensionlessQuantity`,
  `dimensionlessReadout`.
- Angle conversion: `radiansOfDegrees`.
- Figure/physical labels: `OpticalRegion`, `PrismVertex`, `PrismFace`, and
  `RaySegment`.
- Experiment model: `PrismLaserSetup` and
  `angleFromPropagationNormal`.
- Figure and law predicates: `MatchesFigureReadouts`,
  `HasDepictedPrismGeometry`, `HasDepictedRayPath`,
  `HasPhysicalRefractiveIndices`, and `SatisfiesSnellLawAtPrismFaces`.
- Answer representation: `AnswerChoice`, `answerRefractiveIndex`, and
  `MatchesAnswerToNearestHundredth`.
- Derived results: `exit_interface_angles_from_figure` and
  `prism_refractive_index_exact_formula`.
- Blueprint label `thm:physics:phyx_mini_0050:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0050.problem_phyx_mini_0050`.

All declarations other than the final theorem are public supporting helpers;
they should receive blueprint entries if the blueprint is expanded beyond its
current single autoformalization target.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell's law refraction refractive index geometrical
  optics` and likely-name query `snell refractiveIndex optics` exposed no
  applicable optical refraction declaration. Results such as `PolynomialLaw`
  and Mathlib's Euclidean law of sines are not Snell's law.
- Query `physical dimensions angle plane angle radians dimensionless quantity`
  found Physlib `Dimension` (id 394292), Physlib `WithDim`-related entries, and
  Mathlib `Real.Angle` entries. The latter were not used because the figure and
  law use explicit oriented radian representatives rather than angles modulo
  `2π`.
- Query `WithDim dimensionless physical quantity SI units` selected
  `Dimensionful` (id 394284), `WithDim` (id 394425), and `UnitChoices.SI`
  (id 394270).
- Queries `dimensionless quantity WithDim zero dimension` and
  `Dimension.dimensionless unitless dimension` confirmed that Physlib uses
  the multiplicative identity dimension `1` for unit-independent quantities;
  `WithDim.scaleUnit_dim_eq_zero` (id 394464) and
  `UnitChoices.dimScale_one` (id 394261) were supporting evidence but were not
  needed as names in the declarations.
- Query `plane angle radians degree units physical quantity` found
  `Real.Angle`, `Real.Angle.sin`, and `Real.Angle.toReal`; these candidates were
  rejected for the oriented-readout reason above.
- Query `Real.sin Real.pi` confirmed the Mathlib trigonometric family used by
  the explicit `Real.sin` and `Real.pi` expressions.

Module, source, and docstring were fetched before use for `Dimensionful`,
`WithDim`, and `UnitChoices.SI`; module and source were also fetched for
`Dimension`.

## PhysLean/Mathlib names grounded

- Physlib `Dimension`, declared in `Physlib.Units.Dimension`.
- Physlib `Dimensionful` and `UnitChoices.SI`, declared in
  `Physlib.Units.Basic`.
- Physlib `WithDim` and its `val` projection, declared in
  `Physlib.Units.WithDim.Basic`.
- Mathlib `Real.sin`, `Real.pi`, real absolute value, real arithmetic, and order
  relations, imported through
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` and confirmed by Lean
  elaboration.

## Local abstractions introduced

- `OpticalRegion` distinguishes the surrounding air from the prism interior;
  their refractive indices are unit-independent Physlib quantities.
- `PrismVertex`, `PrismFace`, and `RaySegment` preserve the figure's triangle,
  two interfaces, and three stages of beam propagation.
- `PrismLaserSetup` stores the physical property and the oriented radian
  readouts needed to interpret the raster without identifying physical regions
  or ray segments with scalars.
- The figure/path/geometry predicates separate direct readouts and spatial
  relations from the governing optical law.
- `SatisfiesSnellLawAtPrismFaces` is local because no Mathlib/Physlib Snell-law
  declaration was found; it faithfully states `n₁ sin θ₁ = n₂ sin θ₂` at each
  interface and does not contain the requested solution.

## Source/law/answer audit

- Primary image inspected: `phyx_data/test_image/50.png`. It shows a horizontal
  beam entering a vertical prism face, `30°` and `60°` triangle labels, a
  horizontal reference at the exit, and a `22.6°` downward outgoing ray.
- The right angle is supplied by the pictured vertical-left/horizontal-bottom
  prism geometry. The exit-face forward normal is therefore `30°` above the
  incoming horizontal ray, making the exit angles `30°` and `52.6°`.
- With surrounding-air index `1`, Snell's law gives
  `n_prism = sin(52.6°) / sin(30°)`, whose nearest-hundredth displayed answer is
  the recorded choice B, `1.59`. No source/image contradiction was found.

## Grounding gaps and redraft requests

- Mathlib/Physlib exposes no usable geometrical-optics Snell-law or
  refractive-index structure, so the local optical labels and Snell-law
  predicate are necessary.
- The requested `.archon/AGENTS.md` is absent. The project-scoped
  `.archon/prover-modes/physics-formalize.md`, user instructions, `PROGRESS.md`,
  source report, blueprint chapter, and primary image supplied the applicable
  role context.
- The assigned file contains no `/- USER: ... -/` comment.
- The blueprint chapter was not marked `\\leanok` because the explicit write
  permissions restrict this agent to the assigned Lean file and this result
  file. The plan/blueprint agent should add `\\leanok` after review.

## Verification

- `archon-lean-lsp` diagnostics succeeded with exactly three expected
  `declaration uses sorry` warnings, for the two derived lemmas and the final
  theorem, and no failed dependencies.
