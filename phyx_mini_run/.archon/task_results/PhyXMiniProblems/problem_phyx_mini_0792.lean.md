# Autoformalization result: `problem_phyx_mini_0792.lean`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was applied. This iteration addresses the exact review-gate reason,
"physics target does not import Physlib/PhysLean", by importing
`Physlib.SpaceAndTime.Space.CrossProduct` and using Physlib's three-dimensional
Euclidean cross product `Space.«term_⨯ₑ₃_»` directly in the governing law.

## Assumption/target split

### Governing laws

- `SatisfiesVectorProductLaw.resultIsCrossProduct` states the source relation
  `C = A × B` using Physlib's cross product `⨯ₑ₃` on
  `EuclideanSpace ℝ (Fin 3)`.
- The Cartesian-axis definitions use Mathlib's genuine Euclidean vectors and
  `EuclideanSpace.single`; they do not introduce an independent, ungrounded
  vector algebra.
- Mathlib's `InnerProductGeometry.angle` supplies the angle between the input
  vectors. The future magnitude proof is grounded by
  `InnerProductGeometry.norm_ofLp_crossProduct`, which states
  `‖A × B‖ = ‖A‖ * ‖B‖ * sin(angle A B)` for this exact carrier.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Prose and figure/data readouts

- `StatedVectorData` records `‖A‖ = 6`, that `A` points along the positive
  `x` axis, `‖B‖ = 4`, that `B` lies in the `xy` plane, and that its
  unoriented Mathlib angle from `A` is `phiRadians`.
- The primary raster `792.png` was inspected directly. It shows the labelled
  `x`, `y`, and `z` axes, origin `O`, the shaded `xy` plane, all three vector
  labels, and `phi = 30 degrees`. It places `B` on the positive-`y` side of
  `A`; `MatchesSuppliedFigure.vectorBHasPositiveYComponent` retains this
  orientation needed to distinguish the two planar vectors with the same
  unoriented angle.
- `angleMarkMatchesRadians` converts the displayed degree readout to radians.
- The raster draws the arrow labelled `C` along the labelled positive `z`
  direction, but gives no metric scale. Those two facts are retained only as
  fields of `VectorProductFigure`; they are not equated with, or used to
  define, the independent unknown `vectorCInSquaredUnits`.
- `displayedCoefficient` and `displayedAnswerVector` preserve all four literal
  multiple-choice readouts: `15 k-hat`, `12 k-hat`, `8 k-hat`, and
  `18 k-hat`.

### Current target conclusions

- `vectorProduct_eq_twelve_kHat` concludes
  `vectorCInSquaredUnits = 12 • kHat`, the vector shown in answer choice B.

## Goal-faithfulness audit

`VectorProductSetup.vectorCInSquaredUnits` is independent data: it is not
defined as a cross product, an answer choice, or `12 • kHat`. The only premise
that relates it to the inputs is the source's governing law `C = A × B`; no
premise states its magnitude, its Cartesian components, its direction, the
coefficient `12`, or the answer label B.

The drawn `C` arrow's axis and sense remain disconnected raster metadata, so
they do not smuggle even the direction part of the target into the physical
unknown. The positive-`y` condition concerns only input vector `B` and is a
genuine figure readout. Likewise, `displayedAnswerVector .B` is merely the
literal answer-list vector and does not define `C`; the theorem still requires
the magnitudes, angle, orientation, and cross-product law.

The source calls both input magnitudes generic "units" and never identifies
the vectors as displacements, forces, or another named physical quantity.
Accordingly the formalization explicitly models their Cartesian numerical
readouts in one common unnamed vector unit and models `C`'s readout in the
square of that unit. It does not invent a length, force, or SI dimension.

## Source/law/answer audit

- Source: the prose and raster agree that `A` has magnitude 6 along `+x`, `B`
  has magnitude 4 in the `xy` plane, and the directed figure placement from
  `A` toward `B` is `30 degrees` on the positive-`y` side.
- Law: `C = A × B` is represented by Physlib's actual Euclidean cross product,
  not a local final-answer predicate.
- Answer: the supported magnitude is `6 * 4 * sin(30 degrees) = 12`; the
  right-hand orientation from `+x` toward the positive-`y` side gives `+z`.
  Thus `C = 12 k-hat`, consistent with recorded choice B.

## Declarations and blueprint correspondence

- Geometry/readout layer: `SpatialVector`, `CoordinateAxis`, `axisIndex`,
  `axisVector`, `iHat`, `jHat`, `kHat`, `CoordinatePlane`,
  `LiesInCoordinatePlane`, and `PointsAlongPositiveAxis`.
- Figure vocabulary: `FigureVectorLabel`, `AxisSense`, and
  `VectorProductFigure`.
- Independent setup and premise interfaces: `VectorProductSetup`,
  `StatedVectorData`, `MatchesSuppliedFigure`, and
  `SatisfiesVectorProductLaw`.
- Displayed-answer layer: `AnswerChoice`, `displayedCoefficient`, and
  `displayedAnswerVector`.
- `vectorProduct_eq_twelve_kHat` is the main theorem corresponding to
  blueprint label `thm:physics:phyx_mini_0792:target`.

The theorem body is `by sorry`, as required at the autoformalization stage.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `three dimensional Euclidean vector cross product`
  returned and selected Physlib's `Space.«term_⨯ₑ₃_»` (id `392770`), and also
  returned Mathlib's `crossProduct` and
  `InnerProductGeometry.norm_ofLp_crossProduct`.
- Likely-name query `crossProduct` independently found Mathlib's
  `crossProduct` (id `244738`), the component-level operation used internally
  by Physlib's notation.
- Natural-language query `EuclideanSpace coordinate unit vector` returned and
  selected `EuclideanSpace.single` (id `133921`).
- Natural-language query `angle between real inner product space vectors`
  returned the `InnerProductGeometry` angle API, including `cos_angle`,
  `sin_angle_nonneg`, and related lemmas. An LSP `#check` then validated the
  exact signature of `InnerProductGeometry.angle` on the selected carrier.
- Natural-language query
  `physical dimension quantity length vector units cross product` found
  Physlib's `Dimension` and `Dimensionful` infrastructure. Follow-up queries
  `Dimensionful physical quantity arbitrary type EuclideanSpace vector`,
  `CarriesDimension EuclideanSpace vector`, `dimensionful vector physical
  units`, and `UnitChoices Dimensionful` were used to assess whether those
  wrappers matched this problem's unnamed generic vector unit.
- Query `Space physical Euclidean space type definition` distinguished
  Physlib's physical point-space `Space d` from the Euclidean vector carrier
  on which its `⨯ₑ₃` notation is defined.

Source and module data were fetched for `Space.«term_⨯ₑ₃_»`,
`Space.inner_cross_self`, `crossProduct`,
`InnerProductGeometry.norm_ofLp_crossProduct`, `EuclideanSpace.single`,
`Dimension`, `Dimensionful`, `CarriesDimension.toDimensionful`,
`Dimensionful.smul_apply`, and `UnitChoices.dimScale`. The selected module
paths are `Physlib.SpaceAndTime.Space.CrossProduct`,
`Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct`, and
`Mathlib.Analysis.InnerProductSpace.PiL2` (transitively imported).

## Physlib/Mathlib names grounded

- Physlib: `Space.«term_⨯ₑ₃_»` (notation `⨯ₑ₃`) and
  `Space.inner_cross_self`.
- Mathlib: `EuclideanSpace`, `EuclideanSpace.single`, `crossProduct`,
  `InnerProductGeometry.angle`,
  `InnerProductGeometry.norm_ofLp_crossProduct`, `Real.pi`, norms, and real
  scalar multiplication.

A standalone LSP snippet validated both imports, the Physlib cross-product
notation (with `Matrix` and `Space` opened), the Euclidean carrier, unit-vector
constructor, angle, and cross-product norm law.

## Local abstractions introduced

- `SpatialVector` is a descriptive alias for the library type
  `EuclideanSpace ℝ (Fin 3)`. It is not a scalar alias or a replacement vector
  implementation; it identifies that values are Cartesian readouts.
- The finite axis/plane/label/sense types preserve literal raster vocabulary.
  `axisIndex`, `axisVector`, `LiesInCoordinatePlane`, and
  `PointsAlongPositiveAxis` are the smallest coordinate predicates needed to
  express the supplied geometry.
- `VectorProductSetup` keeps the three labelled vector readouts independent.
  Its field names explicitly distinguish the common input unit from the
  squared output unit.
- `SatisfiesVectorProductLaw` groups the one supplied physical relation but
  delegates the operation itself to Physlib. The earlier redundant local
  cross-product transport was removed in this iteration.

## Grounding gaps and redraft requests

- Physlib's `Dimensionful` API requires a specified physical dimension. The
  source gives only generic vector "units", so applying a length, force, or
  other dimension would add unsupported content. Explicitly named numerical
  vector readouts are therefore the faithful model here.
- No missing physics infrastructure required an invented cross-product law;
  Physlib's exact operation is used directly.
- `.archon/AGENTS.md` is absent in this workspace. The complete
  `.archon/prover-modes/physics-formalize.md`, `PROGRESS.md`, exact review-gate
  reason, source report, blueprint chapter, primary raster, and injected task
  instructions supplied the applicable role and retry protocol.
- The advertised `archon` executable is absent from `PATH`, so the read-only
  DAG query could not be run. The source report explicitly records no previous
  parts.
- The blueprint environment was not edited to add `\leanok`, because the
  task's explicit write permissions allow edits only to the assigned Lean file
  and this result file. The plan/coordination agent should add the marker after
  accepting the formalization.

## Verification

- `archon-lean-lsp` diagnostics succeeded with exactly one expected
  `declaration uses sorry` warning and no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0792.lean` exited with
  status `0` and emitted the same one expected warning.
- No-index `git diff --check` checks reported no whitespace errors for either
  permitted output file.
