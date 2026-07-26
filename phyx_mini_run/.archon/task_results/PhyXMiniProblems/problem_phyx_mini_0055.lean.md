# Autoformalization result: `problem_phyx_mini_0055.lean`

## Retry outcome

The iteration-002 formalization gate rejected this target only because no
genuine post-formalization task result existed.  The gate reason explicitly
says that the generic `physics-grounding` preflight predates the revised Lean
model and cannot document the searches, declarations, abstractions, gaps, or
source/law/answer split actually used.  A fresh audit found no semantic defect,
so the current physical statement was preserved as required by the final-retry
protocol.

The blueprint contains `% archon:physics`, so the `physics-formalize`
discipline was used.  The primary image was inspected directly.  It confirms
water on the left with `n₁ = 1.33`, air on the right with `n₂ = 1.00`, the
left-to-right axis, signed radius `R = -25 cm`, object distance `s = 10 cm`,
and a virtual image between the fish and the near spherical surface.  The four
source choices are `14`, `8.6`, `8.3`, and `7.4` centimeters, with recorded
answer C.

## Assumption/target split

### Governing laws

- `h_exactLocalSnellLaw` imposes the exact sine form of Snell's law for all
  sufficiently small signed surface heights.  Incident and refracted angles
  are measured relative to the same outward-normal angle.
- `h_incidentFirstOrderGeometry` gives the incident-direction derivative
  `1/s` at the axial ray.
- `h_sphericalNormalFirstOrderGeometry` gives the spherical-normal derivative
  `-1/R` at the vertex.
- `h_virtualImageFirstOrderBackProjection` characterizes the unknown
  first-order virtual-image location by the refracted-direction derivative
  `1/q`.  It does not specify the value of `q`.
- `h_centralRay` supplies the common zero-angle central configuration needed
  when differentiating the exact sine law.
- Positivity of the two indices and bowl diameter records the physically
  admissible branch and nondegenerate pictured bowl.

### Previous-part results

- None.  The source report's `previous_parts` array is empty.

### Figure/data readouts

- `FishBowlRefractionSetup` records the water and air indices, the center of
  curvature, fish, virtual image, near surface vertex, and bowl diameter.
- `OpticalLength = Dimensionful (WithDim L𝓭 ℝ)` keeps every axial position
  and diameter dimensionful.  `lengthReadout LengthUnit.centimeters` is the
  explicitly named scalar centimeter projection used in the hypotheses.
- `h_waterIndex`, `h_airIndex`, `h_bowlDiameter`, `h_objectDistance`, and
  `h_signedRadius` encode the image readouts `1.33`, `1.00`, `50 cm`, `10 cm`,
  and `-25 cm`.
- `h_radiusDiameterGeometry` records that the pictured spherical radius is
  negative one half of the bowl diameter under the selected orientation.
- `h_axialOrder` records the figure geometry: center, fish, virtual image, and
  surface vertex occur in that left-to-right order.
- `AnswerChoice` and `answerDistanceInCentimeters` retain all four printed
  choices rather than only the recorded answer.

### Current target conclusions

- The positive virtual-image back-projection distance from the near surface is
  exactly `5000/599 cm` in the first-order optical model.
- This exact value differs from choice C's printed `8.3 cm` by at most
  `0.05 cm`, the half-unit at one-decimal-place precision.
- Choice C is uniquely closer to the exact first-order value than each other
  displayed answer.

## Goal-faithfulness audit

No premise contains the exact target distance `5000/599`, the `0.05 cm`
tolerance conclusion, or the unique-nearest-choice conclusion.  The setup
stores an unknown physical `virtualImagePosition`; `h_axialOrder` only locates
it qualitatively, while `h_virtualImageFirstOrderBackProjection` gives the
standard geometric meaning of its unknown distance through a derivative.
That derivative contract cannot make the numeric answer true by unfolding.

The three `HasDerivAt` premises are local little-o contracts at the central
ray, so the formalization does not globalize the paraxial approximation
`sin θ ≈ θ`.  Snell's sine law itself is exact on a neighborhood.  Thus the
conclusion is explicitly about the first-order image, not an unsupported claim
that all finite-angle rays through a spherical interface intersect exactly.

The answer table is source metadata: it records that choice C is `8.3 cm`, but
does not assert that C is correct.  Correctness and unique closeness occur only
in the theorem conclusion.

The source/law/answer calculation is consistent.  At the central ray the
incident, normal, and refracted direction derivatives are respectively
`1/10`, `1/25`, and `1/q`.  Differentiating exact Snell therefore gives

`(133/100) * (1/10 - 1/25) = 1/q - 1/25`,

so `1/q = 599/5000` and `q = 5000/599 ≈ 8.347245 cm`.  Its distance from
`8.3 cm` is about `0.047245 cm`, below `0.05 cm`, and is strictly smaller than
its distance from `8.6`, `7.4`, or `14 cm`.

## Declarations and blueprint correspondence

- `OpticalLength` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-opticallength`.
- `lengthReadout` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-lengthreadout`.
- `FishBowlRefractionSetup` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-fishbowlrefractionsetup`.
- `MeridionalRayFamily` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-meridionalrayfamily`.
- `AnswerChoice` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-answerchoice`.
- `answerDistanceInCentimeters` corresponds to
  `def:physics:phyx-mini-0055:phyxminiproblems-problemphyxmini0055-answerdistanceincentimeters`.
- `problem_phyx_mini_0055` corresponds to
  `thm:physics:phyx_mini_0055:target`.

All six helpers are direct parts of the main target's physical scene, unit
projection, ray model, or answer metadata; no isolated helper was added.  The
blueprint already contains the matching `\lean{...}` pins.  Its environments
are ready for `\leanok`, but the explicit task write permissions make the
chapter read-only; the plan/synchronization lane should add those markers.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural language: `dimensionful physical quantity with length dimension and
  unit readout`.  This grounded Physlib's `Dimensionful`; nearby results were
  dimensional conversion and consistency declarations.
- Likely names: `Dimensionful WithDim L𝓭` and `WithDim`.  These grounded
  `Dimensionful`, `WithDim`, and `Dimension.L𝓭` for the physical length type.
- Natural language/likely name: `length unit centimeters
  LengthUnit.centimeters`.  This grounded `LengthUnit`,
  `LengthUnit.centimeters`, and `Dimension.L𝓭`.
- Likely name: `UnitChoices.SI`.  This grounded the SI unit-choice record used
  when overriding its length field with the selected `LengthUnit`.
- Natural language/likely name: `derivative of a real function at a point
  HasDerivAt`.  This grounded Mathlib's `HasDerivAt` and confirmed from its
  source/docstring that it is exactly a local derivative with a little-o
  remainder.
- Natural language: `eventually in a neighborhood filter nhds`, followed by
  likely name `Filter.Eventually nhds`.  This grounded `Filter.Eventually` and
  its `∀ᶠ` notation for the exact local Snell-law premise.
- Likely name: `Real.sin`.  This grounded Mathlib's real sine function used in
  exact Snell's law.
- Natural language: `Snell law refraction refractive index`.  It returned
  unrelated polynomial laws and Euclidean triangle `law_sin`, but no Snell,
  refractive-index, spherical-refraction, or optical-interface model suitable
  for this theorem.

Source, module, and docstring were fetched only for candidates retained in the
Lean model:

- `Dimensionful` (id `394284`), module `Physlib.Units.Basic`;
- `WithDim` (id `394425`), module `Physlib.Units.WithDim.Basic`;
- `Dimension.L𝓭` (id `394324`), module `Physlib.Units.Dimension`;
- `UnitChoices.SI` (id `394270`), module `Physlib.Units.Basic`;
- `LengthUnit` (id `393137`) and `LengthUnit.centimeters` (id `393160`),
  module `Physlib.SpaceAndTime.Space.LengthUnit`;
- `HasDerivAt` (id `124761`), module
  `Mathlib.Analysis.Calculus.Deriv.Basic`;
- `Real.sin` (id `128819`), module
  `Mathlib.Analysis.Complex.Trigonometric`;
- `Filter.Eventually` (id `284497`), module
  `Mathlib.Order.Filter.Defs`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `WithDim.val`, `Dimension.L𝓭`,
  `UnitChoices.SI`, `LengthUnit`, and `LengthUnit.centimeters`.
- Mathlib: `HasDerivAt`, `Real.sin`, `Filter.Eventually`, `nhds`, real absolute
  value, and ordered-field arithmetic.  The last three were additionally
  confirmed by successful LSP elaboration of the completed statement.

## Local abstractions introduced

- `OpticalLength` is not a transparent scalar alias.  It specializes
  Physlib's dimensionful-quantity infrastructure to the length dimension and
  a dimension-tagged real representation.
- `FishBowlRefractionSetup` preserves the distinct physical roles of diameter
  and four labeled axial positions as dimensionful lengths while keeping the
  two explicitly dimensionless refractive-index readouts real-valued.
- `MeridionalRayFamily` preserves the physical ray-family role and its three
  separately named oriented radian projections.  It is not identified with a
  single scalar.
- The exact local Snell-law hypothesis is a faithful local law interface
  because LeanExplore found no matching Mathlib/Physlib declaration.  Its
  statement uses grounded `Real.sin`, `Filter.Eventually`, and `nhds` rather
  than encoding the desired image distance.
- `AnswerChoice` and `answerDistanceInCentimeters` preserve the multiple-choice
  source and its printed scalar measurements.

## Grounding gaps and redraft requests

- LeanExplore found no ready-made refractive-index type, Snell-law predicate,
  spherical refracting-surface model, or meridional optical ray family in
  Mathlib/Physlib.  The minimal local scene/ray interfaces and exact law
  hypothesis are therefore necessary.
- No source/image contradiction, dimensional defect, sign-convention defect,
  or answer correction was found.  No Lean statement redraft is requested.
- The requested `.archon/AGENTS.md` is absent.  The invocation's role rules,
  `.archon/PROGRESS.md`, and the complete
  `.archon/prover-modes/physics-formalize.md` were used instead.
- The invocation says `archon` is on `PATH`, but both requested read-only DAG
  commands failed with `archon: command not found`.  The blueprint's explicit
  `\uses{...}` list and the source report independently show the local helper
  dependencies and absence of previous parts.

## Prover result (iteration 012)

The sole `sorry` in `problem_phyx_mini_0055` was replaced by a complete proof
of the unchanged theorem statement.

- The incident-minus-normal and refracted-minus-normal derivatives are formed
  with `HasDerivAt.sub`.
- `HasDerivAt.sin` and `HasDerivAt.const_mul`, together with the three
  zero-angle central-ray equalities, compute both derivatives of the exact
  local Snell identity.
- `HasDerivAt.congr_of_eventuallyEq` transports the right-hand derivative
  across `h_exactLocalSnellLaw`, and uniqueness of the derivative gives
  `(133/100) * (1/10 - 1/25) = 1/q - 1/25`.
- The positive image distance follows from `h_axialOrder`; `field_simp` and
  `nlinarith` then solve the reciprocal equation as `q = 5000/599`.
- The tolerance and all four answer-choice branches are exact rational
  calculations discharged by `norm_num`.

There are no remaining `sorry`, `admit`, `axiom`, or `sorryAx` occurrences in
the assigned Lean file. No statement redraft is needed.

The blueprint theorem environment is ready for `\leanok`. It was not edited
because this prover's explicit write permissions restrict changes to the
assigned Lean file and this task-result file.

## Verification

- Fresh Lean LSP diagnostics: no errors, warnings, or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0055.lean`: exit code `0`;
  no `sorry` warning. The only output consists of four unused-hypothesis
  lints for frozen statement premises.
- Root `lake build`: completed successfully with four jobs.
- Axiom/source audit of
  `PhyXMiniProblems.ProblemPhyXMini0055.problem_phyx_mini_0055`: only the
  standard imported axioms `propext`, `Classical.choice`, and `Quot.sound`;
  source-scan warnings are empty.

## Redraft needed

None.
