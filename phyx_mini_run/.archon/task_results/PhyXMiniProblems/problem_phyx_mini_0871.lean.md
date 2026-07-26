# PhyXMiniProblems/problem_phyx_mini_0871.lean

## Summary

- Created the previously absent Lean file for the `% archon:physics` chapter.
- Formalized the primary-image electrostatics model with dimensionful
  potential, length, planar position, and electric-field quantities.
- Added one derived magnitude lemma and the blueprint target theorem, both
  with the required `by sorry` bodies.
- Verified with
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0871.lean`; it exits 0
  with only the two expected `declaration uses sorry` warnings.

## Assumption/target split

### Governing laws

- `SatisfiesUniformEquipotentialElectrostatics.potentialConstantOnShownLine`
  states that potential is constant along each represented equipotential.
- `fieldAtDotIsNormalToLines` states that the field at the marked point is a
  signed multiple of the unit normal pointing toward increasing potential.
- `uniformFieldPotentialDrop` states the general constant-field relation
  `V(q) - V(p) = - E · (q - p)` throughout the depicted uniform region.
- `fieldReadoutAgreesWithPhyslib` connects the dimensionful SI field readout
  to `Electromagnetism.ElectricField 2` at the observation time and marked
  position.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- `MatchesPrimaryEquipotentialFigure` records axes labelled `x` and `y`;
  three visible, parallel, dashed green lines; labels `-200 V`, `0 V`, and
  `200 V`; a black dot on the middle line; two perpendicular gaps labelled
  `1 cm`; and the printed `45°` angle.
- The same structure calibrates the adjacent physical spacing to `1/100 m`,
  the three independent potential observables to their displayed voltages,
  and the representative-point displacements to the increasing-potential
  normal.
- `HasPhysicalEquipotentialGeometry` contains only positivity and unit-vector
  normalization conditions.

### Current target conclusions

- `electricFieldMagnitudeAtDot_from_adjacentEquipotentials` derives the
  potential-change-over-normal-distance magnitude relation.
- `electricFieldMagnitudeAtDot_matches_answer_D` concludes that the magnitude
  is `20 kV/m`, that D displays `20 kV/m`, and that D is the unique exact
  displayed match.

## Goal-faithfulness audit

- No premise field mentions `20 kV/m`, answer D, or any selected answer.
- `electricFieldAtMarkedPoint` is an independent dimensionful observable; it
  is not defined as a voltage difference divided by the displayed spacing.
- The numeric field magnitude occurs only in the target theorem.  The answer
  table is a literal transcription of all four choices, while
  `IsUniqueExactDisplayedMatch` is a choice-generic comparison predicate.
- The `1 cm` spacings and voltage labels are legitimate primary-image
  measurements.  The field conclusion still requires the independent
  electrostatic potential-drop and normality laws.
- No `True`, reflexive target, scalar alias for a physical primitive, axiom,
  or definition-unfolding shortcut was introduced.

## Declarations created and blueprint alignment

- Physical dimensions and quantity/readout vocabulary:
  `electricPotentialDimension`, `electricFieldDimension`, `LengthQuantity`,
  `ElectricPotentialQuantity`, `PlanarPositionQuantity`,
  `ElectricFieldVectorQuantity`, `lengthInMeters`,
  `electricPotentialInVolts`, `positionVectorInMeters`,
  `positionInPhyslibSpace`, and `electricFieldVectorInVoltsPerMeter`.
- Figure/setup vocabulary: `PotentialLine`, `AdjacentLineGap`,
  `CoordinateAxis`, `FigureColor`, `EquipotentialLineFigure`, and
  `EquipotentialFieldSetup`.
- Assumption interfaces: `MatchesPrimaryEquipotentialFigure`,
  `HasPhysicalEquipotentialGeometry`, and
  `SatisfiesUniformEquipotentialElectrostatics`.
- Target vocabulary: `electricFieldMagnitudeAtDotInVoltsPerMeter`,
  `electricFieldMagnitudeAtDotInKilovoltsPerMeter`, `AnswerChoice`,
  `displayedFieldMagnitudeInKilovoltsPerMeter`, and
  `IsUniqueExactDisplayedMatch`.
- Derived lemma:
  `electricFieldMagnitudeAtDot_from_adjacentEquipotentials`.
- Blueprint label `thm:physics:phyx_mini_0871:target` corresponds to
  `electricFieldMagnitudeAtDot_matches_answer_D`.
- The explicit write restrictions prohibit editing the blueprint chapter, so
  the review agent should add `\leanok` to that theorem environment.

## LeanExplore grounding

All searches used `packages: ["Mathlib", "Physlib"]`.

Queries actually issued:

- `electric field equals negative gradient of electric potential equipotential lines`
- `Electromagnetism.ElectricField`
- `Dimensionful WithDim electric field potential dimension`
- `Physlib Space physical position spacetime`
- `WithDim`

Candidates inspected:

- `Electromagnetism.ElectricField` (used), from
  `Physlib.Electromagnetism.Basic`: a field is
  `Time → Space d → EuclideanSpace ℝ (Fin d)`.
- `Dimensionful` (used), from `Physlib.Units.Basic`: a unit-covariant physical
  quantity represented across `UnitChoices`.
- `WithDim` (used), from `Physlib.Units.WithDim.Basic`: a type tagged by an
  explicit `Dimension`, with its carrier exposed through `WithDim.val`.
- `Space` (used), from `Physlib.SpaceAndTime.Space.Basic`: Physlib's affine
  Euclidean position type.  `positionInPhyslibSpace` explicitly embeds the
  dimensionful position's coherent-SI coordinates for field evaluation.
- `Electromagnetism.ElectromagneticPotential.electricField` and
  `electricField_eq` (inspected, not used), from
  `Physlib.Electromagnetism.Kinematics.ElectricField`: these give
  `E = -∇φ - ∂ₜA`.  They require a full electromagnetic four-potential and
  vector-potential time derivative, which is more machinery than the static,
  figure-derived finite-difference problem supplies.

Names additionally syntax-checked in an LSP snippet were `WithDim`,
`EuclideanSpace`, `inner`, `Time`, `Space`, and coherent-SI evaluation through
`UnitChoices.SI`.

## Local abstractions introduced

- The potential and field dimensions are composed from Physlib base
  dimensions rather than collapsed to `ℝ`.
- `EquipotentialLineFigure` preserves the literal axis labels, colors, dashed
  styling, voltage text, black dot, spacing arrows, and angle from the image.
- `EquipotentialFieldSetup` keeps potential, field, and geometry independent;
  it also carries predicates for line membership and the depicted uniform
  region so that equipotential and field laws are genuinely general.
- `SatisfiesUniformEquipotentialElectrostatics` is the smallest local law
  interface needed after the full `ElectromagneticPotential` API proved too
  broad for this static problem.

## Grounding gaps

- LeanExplore exposed no ready-made Physlib declaration specifically modeling
  labelled equipotential-line diagrams or the finite-difference law for a
  uniform electrostatic field.  The local law interface therefore states that
  physics directly.
- `.archon/AGENTS.md` was absent, although the requested mode instructions
  were available in `.archon/prover-modes/physics-formalize.md` and were
  followed.
- The `archon` executable advertised for DAG navigation was not on `PATH`, so
  no dependency-node metadata could be retrieved.  The chapter contains no
  named prerequisite declarations and the source report lists no previous
  parts.
- The blueprint theorem text is only a generic autoformalization directive,
  not an informal derivation.  The physical statement and model were grounded
  from the source report and primary image, as the chapter explicitly directs.

## Source/law/answer audit

- The primary raster `phyx_data/test_image/871.png` shows three parallel dashed
  green lines, with the marked dot on the central line, and the two `1 cm`
  measurement arrows aligned with their common up-right normal.  Thus the
  relevant adjacent potential change is `200 V` over a perpendicular distance
  of `0.01 m`; the pictured `45°` fixes orientation but does not add a
  `sqrt 2` factor to that measured normal spacing.
- The local governing-law interface states the uniform-field potential-drop
  relation and normality independently of the answer table.
- The supported result is exactly `20 kV/m`, matching recorded choice D; no
  source/law/answer inconsistency or redraft is required.

## Redraft requests

- None for the Lean statement.  The plan/review agent may wish to expand the
  blueprint proof with the explicit calculation `200 V / 0.01 m = 20 kV/m`
  and then mark the theorem environment with `\leanok`.

## Why I stopped

Real progress: the complete physics formalization and its target theorem were
introduced and compile with exactly the expected `sorry` warnings.
