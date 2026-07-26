# Autoformalization result: `problem_phyx_mini_0049.lean`

- Archon iteration: `002`
- Mode: `physics-formalize` (the chapter contains `% archon:physics`)
- Lean file: `PhyXMiniProblems/problem_phyx_mini_0049.lean`
- Blueprint target: `thm:physics:phyx_mini_0049:target`
- Retry reason addressed: this is the required genuine post-formalization
  report, based on the completed Lean model, direct source/image inspection,
  actual LeanExplore searches, and final compiler diagnostics.

## Assumption/target split

### Governing laws

- `SatisfiesSnellsLawAt` states the general interface law
  `n₁ sin θ₁ = n₂ sin θ₂` for the entry and exit faces.  It contains
  no fixed outgoing angle or answer label.
- `ObeysSnellsLaw.atInterface` applies that law at both interfaces.
- `SatisfiesParallelSheetGeometry` records equal propagation-oriented normals
  and tangents for the parallel faces, perpendicular normal/tangent directions,
  geometric angle readouts from nonzero ray vectors, preservation of the
  internal angle across the parallel faces, and the complement relation between
  the incoming elevation above the sheet and its incidence angle from the
  normal.
- `HasPhysicalOpticalParameters` records positive dimensionless refractive
  indices and selects the principal acute branch for every measured ray angle.
  These branch conditions are needed to recover angle equality from equality of
  sines.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `ParallelGlassSheetDiagram.thickness` is a genuine Physlib dimensionful
  length. `MatchesGlassSheetProblemData.thicknessReadout` assigns the stated
  `1.0 cm` value through `oneCentimeter`.
- `incomingElevationRadians` is a scalar radian readout above the sheet
  surface, and the problem-data premise assigns it `30°` via
  `degreesToRadians`.
- `OpticalRegion` distinguishes the incident air, glass, and emergent air.
  `sameAmbientAirOnBothSides` states only that the two exterior regions have
  equal refractive-index readouts; the glass index remains arbitrary and
  positive.
- `RayDirection` uses Mathlib's `RayVector` over a two-dimensional
  `EuclideanSpace`, so every ray and face direction is geometric and nonzero.
- All answer-choice degree readouts are retained by
  `AnswerChoice.directionDegrees`; `recordedAnswerChoice` stores dataset
  metadata but is not a premise.
- Direct inspection confirmed that source image `49.png` depicts an unrelated
  mirror room. `AuxiliaryMirrorRoomFigure` and
  `MatchesAuxiliaryMirrorRoomImage` preserve its `2.50 m`, `1.00 m`, `0.50 m`,
  `1.50 m`, `0.50 m`, `l₁`, `l₂`, `θ₁`, and `θ₂` labels separately; none
  is used by the glass-sheet theorem.

### Current target conclusions

- `outgoingDirectionIsAnswerB` concludes that the outgoing ray's angle from
  the propagation-oriented normal of the exit face is
  `degreesToRadians AnswerChoice.B.directionDegrees`, hence `60°`.
- This convention reconciles the given `30°` elevation above the sheet
  surface with recorded choice B: the two readouts are complementary.

## Goal-faithfulness audit

The requested exit angle and choice B occur only in the conclusion of
`outgoingDirectionIsAnswerB`. No field of `ParallelGlassSheetDiagram`,
`MatchesGlassSheetProblemData`, `HasPhysicalOpticalParameters`,
`SatisfiesParallelSheetGeometry`, or `ObeysSnellsLaw` assigns an outgoing
angle. The premise structures contain only source data, general interface
physics, angle branches, and parallel-plane geometry.

`degreesToRadians` is a general unit conversion, and
`AnswerChoice.directionDegrees` faithfully lists all four displayed choices;
neither defines the physical outgoing angle. The substantive conclusion cannot
be obtained by unfolding a helper. It requires combining the input complement
relation, both Snell equations, equal exterior indices, parallel-face internal
geometry, positivity, and acute-branch injectivity. The thickness is preserved
as setup data even though it cancels from the direction result for a
parallel-sided sheet.

The physical ray primitive is not collapsed to a scalar alias:
`RayDirection` is the grounded subtype of nonzero Euclidean vectors. Real
numbers are used only for explicitly named dimensional or dimensionless
readouts: refractive indices, radian angle components, and auxiliary-image
meter measurements.

## Declarations created

- Unit/geometry support: `DimLength`, `centimeterUnitChoices`,
  `oneCentimeter`, `degreesToRadians`, `DiagramPlane`, `RayDirection`, and
  `angleBetweenDirections`.
- Physical roles: `OpticalRegion`, `SheetInterface`, `RaySegment`,
  `incidentRegion`, `transmittedRegion`, `incidentSegment`, and
  `transmittedSegment`.
- Model and assumptions: `ParallelGlassSheetDiagram`,
  `IsPhysicalAcuteAngle`, `MatchesGlassSheetProblemData`,
  `HasPhysicalOpticalParameters`, `SatisfiesParallelSheetGeometry`,
  `SatisfiesSnellsLawAt`, and `ObeysSnellsLaw`.
- Mismatched source-image preservation: `AuxiliaryMirrorRoomFigure` and
  `MatchesAuxiliaryMirrorRoomImage`.
- Answer model: `AnswerChoice`, `AnswerChoice.directionDegrees`, and
  `recordedAnswerChoice`.
- `outgoingDirectionIsAnswerB` formalizes blueprint label
  `thm:physics:phyx_mini_0049:target`.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell's law refraction refractive index sine
  incident transmitted angle` returned real-angle sine and Euclidean triangle
  sine-law declarations, but no optics Snell-law declaration. The likely-name
  query `Snell` likewise returned `Real.Angle.sin`, `Real.sin`, and unrelated
  declarations rather than a refraction law. This directly grounds the need
  for the local `SatisfiesSnellsLawAt` predicate.
- Query `RayVector nonzero vector direction` returned `RayVector` (ID 251775),
  `RayVector.coe`, and ray representative declarations. `RayVector` was
  selected because its fetched source is the subtype `{v : M // v ≠ 0}`.
- Query `InnerProductGeometry.angle angle between vectors` returned
  `InnerProductGeometry.angle` (ID 228174) and its basic properties. The
  selected definition is the undirected real-valued angle computed with
  `Real.arccos`.
- Query `EuclideanSpace real finite dimensional inner product space` returned
  `EuclideanSpace` (ID 133893), which is used with `Fin 2` for the ray diagram.
- Queries `Dimensionful WithDim length UnitChoices centimeters`, `WithDim`,
  `Dimension.L𝓭 length dimension`, and `UnitChoices.SI` returned and motivated
  `Dimensionful` (ID 394284), `WithDim` (ID 394425), `Dimension.L𝓭`
  (ID 394324), `UnitChoices.SI` (ID 394270),
  `LengthUnit.centimeters` (ID 393160), and
  `CarriesDimension.toDimensionful` (ID 394290).
- Query `Real.sin` selected `Real.sin` (ID 128819) for the scalar-radian form
  of Snell's law.

Source, module, and docstring were fetched for every selected candidate above.
The modules are `Mathlib.Analysis.Complex.Trigonometric` (`Real.sin`),
`Mathlib.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace`),
`Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic`
(`InnerProductGeometry.angle`), `Mathlib.LinearAlgebra.Ray` (`RayVector`),
`Physlib.Units.Basic` (`Dimensionful`, `UnitChoices.SI`, and
`CarriesDimension.toDimensionful`), `Physlib.Units.Dimension`
(`Dimension.L𝓭`), `Physlib.Units.WithDim.Basic` (`WithDim`), and
`Physlib.SpaceAndTime.Space.LengthUnit` (`LengthUnit.centimeters`).

## PhysLean/Mathlib names grounded

- Mathlib: `EuclideanSpace`, `RayVector`, `InnerProductGeometry.angle`,
  `Real.sin`, `Real.pi`, and `Fin 2`.
- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices.SI`,
  `LengthUnit.centimeters`, and `CarriesDimension.toDimensionful` (used through
  the opened namespace).
- The language server and standalone Lean compiler accepted all final names
  and signatures.

## Local abstractions introduced

- `ParallelGlassSheetDiagram` is the smallest local setup preserving the
  dimensionful sheet, three material roles, nonzero ray directions, two
  interfaces, face directions, and measured angles.
- `SatisfiesParallelSheetGeometry` separates general parallel-face geometry
  from problem readouts and from Snell physics. It does not encode the target
  output.
- `SatisfiesSnellsLawAt` and `ObeysSnellsLaw` are faithful local governing-law
  interfaces necessitated by the absence of a Mathlib/Physlib optics API.
- The auxiliary-image structures isolate the mismatched source evidence so it
  is preserved without allowing an unrelated mirror diagram to influence the
  glass theorem.

## Grounding gaps

- LeanExplore exposed no dedicated refractive-index, optical-medium, Snell-law,
  or parallel-glass-slab declaration in Mathlib/Physlib. The local optical
  abstractions above were therefore required.
- The requested `.archon/AGENTS.md` is absent. The applicable role discipline
  was recovered from `.archon/prover-modes/physics-formalize.md`, together with
  `PROGRESS.md`, the invocation, the blueprint, the source report, and direct
  image inspection. There are no file-specific `/- USER: ... -/` comments.
- The `archon` executable was not available on `PATH`, so the optional DAG
  queries could not run. The source report independently establishes that
  there are no previous-part dependencies.

## Verification and redraft requests

- Lean language-server diagnostics report success with only the expected
  `sorry` warning on `outgoingDirectionIsAnswerB`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0049.lean` exits with code
  zero and reports the same single warning.
- A source redraft should explicitly say that the requested outgoing direction
  is measured from the exit-face normal. Without that convention, `30° above
  the glass` would ordinarily describe the outgoing elevation above the
  parallel surface as `30°`, while the recorded `60°` answer is its complement.
- The blueprint theorem is ready for `\leanok`, but the chapter was not edited
  because the task's explicit write permissions allow changes only to the
  assigned Lean file and this task-result file.
