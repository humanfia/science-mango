# Autoformalization result: `problem_phyx_mini_0874.lean`

## Assumption/target split

### Governing laws

- `IsStaticUniformElectricField.fieldIsConstant` states that the PhysLean
  spacetime electric field is constant and agrees with the independent
  dimensionful electric-field vector at its coherent-SI readout boundary.
- `SatisfiesUniformFieldPotentialLaw.differenceIsEndpointPotentialChange`
  fixes the orientation of each potential difference as
  `V(endPoint) - V(startPoint)` for every ordered pair of diagram points.
- `SatisfiesUniformFieldPotentialLaw.endpointPotentialChangeFromField` states
  the general constant-field law
  `V(endPoint) - V(startPoint) = -E · (r(endPoint) - r(startPoint))` for every
  ordered pair. It is not specialized to points `A`, `B`, or the value
  `-70 V`.
- `lengthInCentimeters_eq_oneHundred_mul_lengthInMeters` records the unit
  conversion needed to turn the image's centimetre annotations into coherent
  SI metre readouts.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- The primary raster `874.png` contains labelled point dots `A` and `B` and
  three parallel magenta arrows pointing right.
- The field label is `1000 V/m`.
- Point `B` is horizontally `7 cm` to the right of point `A` and vertically
  `3 cm` below it.
- The right and up diagram directions are modeled as an orthonormal frame;
  the displacement from `A` to `B` is the positive horizontal component minus
  the positive vertical component.
- `MatchesSuppliedUniformFieldFigure` calibrates the literal raster readouts
  to independent dimensionful lengths and an electric-field vector.
- The four displayed scalar answer readouts are `12`, `-14`, `-200`, and
  `-70` volts, and the source dataset records label `D`. These are answer/data
  metadata, not physics assumptions used to determine the potential.

### Current target conclusions

- The requested orientation is `V_B - V_A`, represented by
  `setup.potentialDifference .A .B`.
- The target theorem concludes that its coherent-SI readout is `-70 V`.
  The `3 cm` vertical displacement is perpendicular to the rightward field
  and therefore contributes zero to the dot product.

## Goal-faithfulness audit

The potential difference is an independent field of
`UniformElectricFieldSetup`; it is not defined from the field magnitude,
displacement, recorded answer label, or the number `-70`.
`MatchesSuppliedUniformFieldFigure`, `HasDisplayedPointGeometry`,
`HasPhysicalUniformFieldData`, and `IsStaticUniformElectricField` contain only
image readouts, calibration, geometry, positivity, and uniformity. The
potential-law structure states a governing relation uniformly over every
ordered pair of diagram points and contains neither `-70` nor answer choice
`D`. Thus the numerical conclusion first occurs in the substantive target
theorem (apart from the separately identified answer-choice metadata).

The theorem concludes the potential-difference value directly; it is not
closed by unfolding an answer table or a predicate defined to be the desired
answer. The negative sign is fixed by the explicit endpoint orientation and
the electrostatic law rather than by assuming the recorded answer.

## Declarations and blueprint correspondence

- Namespace: `PhyXMiniProblems.ProblemPhyXMini0874`.
- Dimensions and physical types: `electricPotentialDimension`,
  `electricFieldDimension`, `LengthQuantity`, `PositionQuantity`,
  `ElectricFieldVectorQuantity`, `ElectricPotentialQuantity`, and
  `PotentialDifferenceQuantity`.
- Named unit readouts: `lengthReadout`, `lengthInMeters`,
  `lengthInCentimeters`, `positionInMeters`,
  `electricFieldInVoltsPerMeter`, `electricPotentialInVolts`, and
  `potentialDifferenceInVolts`.
- Unit lemma: `lengthInCentimeters_eq_oneHundred_mul_lengthInMeters`.
- Image vocabulary/data: `DiagramPoint`, `FieldArrowLabel`,
  `DiagramDirection`, `PrintedElectricFieldUnit`, `PrintedLengthUnit`, and
  `UniformElectricFieldFigure`.
- Independent setup: `UniformElectricFieldSetup`.
- Premise interfaces: `MatchesSuppliedUniformFieldFigure`,
  `HasDisplayedPointGeometry`, `HasPhysicalUniformFieldData`,
  `IsStaticUniformElectricField`, and `SatisfiesUniformFieldPotentialLaw`.
- Answer metadata: `AnswerChoice`,
  `AnswerChoice.displayedPotentialDifferenceInVolts`, and
  `recordedDatasetAnswer`.
- `problem_phyx_mini_0874` formalizes blueprint label
  `thm:physics:phyx_mini_0874:target`.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query: `electric potential difference in a uniform
  electric field equals negative line integral or negative dot product`.
  - Used `Electromagnetism.ElectricField` (ID 385559) as the packaged
    spacetime field type.
  - The electromagnetic-potential candidates were inspected as near matches
    but were not used because they model a substantially more general
    spacetime potential rather than this elementary static two-point setup.
- Likely-name query: `ElectricPotential electricField potentialDifference`.
  - Confirmed `Electromagnetism.ElectricField` and the absence of a matching
    packaged scalar potential-difference abstraction in the returned results.
- Natural-language query: `SI voltage volt per meter physical quantity units`.
  - Used `UnitChoices.SI` (ID 394270) and
    `LengthUnit.centimeters` (ID 393160).
  - `WithDim.scaleUnit_val` (ID 394460) grounds the later proof route for the
    centimetre/metre conversion lemma.
- Natural-language query: `EuclideanSpace dotProduct real finite dimensional
  coordinate vector`.
  - Used Mathlib's `dotProduct` (ID 210032) for `E · Δr` and its module
    `Mathlib.Data.Matrix.Mul`.
- Natural-language query: `Dimensionful WithDim unit independent physical
  quantity`.
  - Used `Dimensionful` (ID 394284) together with `WithDim` to keep physical
    quantities independent of any particular unit choice.

Source and module information was fetched for the candidates actually used in
the model or intended proof route: `Electromagnetism.ElectricField`,
`UnitChoices.SI`, `LengthUnit.centimeters`, `WithDim.scaleUnit_val`,
`dotProduct`, and `Dimensionful`.

## PhysLean/Mathlib names grounded

- PhysLean: `Dimension`, `Dimensionful`, `WithDim`, `UnitChoices.SI`, `M𝓭`,
  `L𝓭`, `T𝓭`, `C𝓭`, `LengthUnit.meters`, `LengthUnit.centimeters`, and
  `Electromagnetism.ElectricField`.
- Mathlib: `EuclideanSpace`, `NNReal`, and `dotProduct`.

## Local abstractions introduced

- Explicit electric-potential and electric-field dimensions preserve volts
  and volts-per-metre as physical dimensions because the search did not
  identify dedicated packaged scalar aliases for these textbook quantities.
- `Dimensionful (WithDim ... ...)` is used instead of real aliases, so changing
  unit choices changes readout coordinates while preserving the underlying
  physical quantity.
- `UniformElectricFieldFigure` and its finite vocabularies preserve the point
  labels, three distinct arrows, directions, dimension arrows, unit glyphs,
  and printed values from the supplied raster.
- `UniformElectricFieldSetup` keeps physical responses independent from image
  data and answer metadata.
- The local geometry, uniform-field, and potential-law structures are the
  smallest interfaces needed to express the primary-image model and the
  general electrostatic law without assuming the current numerical answer.

## Grounding gaps and redraft requests

- LeanExplore found PhysLean's general spacetime electric-field and
  electromagnetic-potential APIs, but no packaged declaration directly
  expressing the elementary uniform electrostatic relation
  `ΔV = -E · Δr` with dimensionful endpoint potentials. The general local
  `SatisfiesUniformFieldPotentialLaw` interface therefore preserves this law
  explicitly.
- `Electromagnetism.ElectricField` itself has real-vector values and does not
  carry physical units. The model consequently pairs it with an independent
  dimensionful electric-field vector and an explicit uniformity/readout
  bridge.
- The required `.archon/AGENTS.md` is absent from this checkout. The supplied
  task prompt and `.archon/prover-modes/physics-formalize.md` were used as the
  governing instructions.
- The prompt advertises `archon` on `PATH`, but `archon dag-query` could not be
  run because the executable is not installed in this environment.
- The blueprint theorem environment still needs `\leanok`. It was not edited
  because the explicit write permissions restrict this task to the assigned
  Lean file and this task-result file.

## Verification

- `archon-lean-lsp` diagnostics report no errors and exactly two expected
  `declaration uses sorry` warnings, for the unit-conversion lemma and the
  target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0874.lean` exits with code
  `0` and reports only those two expected warnings.
