## Assumption/target split

### Governing laws

- `SatisfiesBaseFaceDiagonalGeometry.rOneComponents` states the rectangular-face vector-addition law
  `R₁ = a iHat + b jHat` in every coherent unit system.
- `SatisfiesBodyDiagonalRightTriangle.displacementComposition` states the figure's path-composition law
  `R₂ = R₁ + c kHat` in every coherent unit system.
- `SatisfiesBodyDiagonalRightTriangle.legsPerpendicular` records that `R₁` and the vertical `c kHat` leg are perpendicular, so the stated triangle is genuinely right-angled rather than merely three vectors satisfying an addition relation.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- `RectangularParallelepipedSetup.edgeLength` stores the three dimensionful physical edge lengths indexed by the printed labels `a`, `b`, and `c`.
- `RectangularParallelepipedSetup.displacement` stores the dimensionful arrows indexed by `R1` and `R2`.
- `MatchesSuppliedFigure` records that the box is rectangular; the `x`, `y`, and `z` labels are shown; `a`, `b`, and `c` align with those axes respectively; both arrows begin at `O`; `R₁` is the base-face diagonal; `R₂` is the body diagonal; and the shaded `R₁`, `c kHat`, `R₂` triangle is shown.
- `HasPositiveEdgeLengths` selects the nondegenerate physical box branch.
- `displayedBodyDiagonalReadout` transcribes all four answer expressions exactly, and `recordedDatasetAnswer` records dataset answer C. These are answer metadata, not theorem premises.

### Current target conclusions

- For every coherent `UnitChoices`, the physical body-diagonal readout is
  `R₂ = a iHat + b jHat + c kHat`.
- The same physical vector agrees with displayed answer C via `MatchesDisplayedBodyDiagonal setup .C`.

## Goal-faithfulness audit

The exact three-component expansion of `R₂` occurs only in the conclusion of `problem_phyx_mini_0682` and in the independent transcription of displayed choice C. No premise field asserts `R₂ = a iHat + b jHat + c kHat` or that the physical vector is answer C.

The two geometry premises preserve the actual reasoning split supplied by the problem: first obtain the base diagonal `R₁ = a iHat + b jHat`, then use the explicitly stated right-triangle composition `R₂ = R₁ + c kHat`. The perpendicularity field captures the right-angle claim but cannot by itself determine `R₂`. `MatchesSuppliedFigure` contains only roles, endpoints, axis-label assignments, and visible marks; it contains no component equality.

`displayedBodyDiagonalReadout` does contain the printed formulas for all four choices, as required to formalize the multiple-choice data, but it never identifies any one of them with the physical displacement. Unfolding this answer table alone cannot prove either target conclusion.

The edge lengths use Physlib dimensionful quantities over `NNReal`, and the displacement uses a Physlib dimensionful quantity whose underlying readout is `EuclideanSpace ℝ (Fin 3)`. Real values appear only after selecting coherent units. Thus the formalization does not collapse physical lengths or displacement vectors to transparent scalar aliases.

## Declarations and blueprint labels

- Blueprint `thm:physics:phyx_mini_0682:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0682.problem_phyx_mini_0682`.
- Dimensionful quantities and readouts: `LengthQuantity`, `SpatialDisplacement`, `lengthReadout`, and `displacementReadout`.
- Cartesian basis vectors: `iHat`, `jHat`, and `kHat`.
- Figure vocabulary: `CoordinateAxis`, `DimensionLabel`, `FigureVectorLabel`, `FigurePointLabel`, `VectorRole`, and `SuppliedParallelepipedFigure`.
- Physical setup and premise interfaces: `RectangularParallelepipedSetup`, `MatchesSuppliedFigure`, `HasPositiveEdgeLengths`, `SatisfiesBaseFaceDiagonalGeometry`, and `SatisfiesBodyDiagonalRightTriangle`.
- Answer vocabulary: `AnswerChoice`, `displayedBodyDiagonalReadout`, `recordedDatasetAnswer`, and `MatchesDisplayedBodyDiagonal`.

The blueprint chapter was not edited to add `\leanok`: the task's explicit write-permission section permits edits only to the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

All searches were run with `packages: ["Mathlib", "Physlib"]`.

Queries included:

- Natural language: `dimensionful physical quantity length SI units`, `Dimensionful length arithmetic addition scalar multiplication`, and `Dimensionful vector physical quantity`.
- Likely names: `DimLength`, `WithDim physical dimension tagged quantity`, `EuclideanSpace`, and `EuclideanSpace.single`.
- Vector/basis concepts: `EuclideanSpace standard orthonormal basis vector Fin` and `Pi.single coordinate basis vector`.
- Geometry concepts and likely names: `rectangular parallelepiped body diagonal vector`, `RectangularParallelepiped`, and `axis-aligned box Euclidean space diagonal`.
- Affine-vector concept check: `displacement vector endpoint subtraction affine space`.

Candidates adopted and source-checked:

- `Dimensionful` (id 394284), from `Physlib.Units.Basic`.
- `WithDim` (id 394425), from `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` (id 394324), from `Physlib.Units.Dimension`.
- `EuclideanSpace` (id 133893), from `Mathlib.Analysis.InnerProductSpace.PiL2`.
- `EuclideanSpace.single` (id 133921), from `Mathlib.Analysis.InnerProductSpace.PiL2`.

`EuclideanSpace.basisFun` (id 133999) was source-checked as an alternative standard orthonormal basis, but `EuclideanSpace.single` was the smaller API needed for the three named unit vectors.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`, and `UnitChoices.SI`.
- Mathlib: `EuclideanSpace`, `EuclideanSpace.single`, `Fin`, `NNReal`, and the real inner product `inner ℝ`.

The LSP snippet check confirmed that `Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 3)))` elaborates, that its selected-unit value projects to a three-dimensional Euclidean vector, and that real length readouts can scale the standard basis vectors.

## Local abstractions introduced

- `SpatialDisplacement` is a unit-independent, length-dimensioned Euclidean vector quantity. It is local because no searched declaration directly combined Physlib dimensions with this problem's named three-dimensional arrows.
- `SuppliedParallelepipedFigure` and the label inductives preserve the primary image's named axes, dimensions, origin, corners, arrows, and arrow roles without forcing any target formula.
- The two `Satisfies...Geometry` structures express the minimal physical geometry used in the informal solution: base-face vector addition, path composition around the shaded triangle, and perpendicularity.

These abstractions preserve the physical distinction between a nonnegative edge length, a signed vector displacement, a dimensionless unit vector, and a coordinate readout in selected units.

## Grounding gaps and redraft requests

- LeanExplore returned Mathlib's `parallelepiped`, `Module.Basis.parallelepiped`, `parallelepiped_single`, and `BoxIntegral.Box`. These model sets generated by linear combinations or boxes used for integration; they do not provide the named, dimensionful `R₁`/`R₂` arrow geometry required here. No Physlib declaration for a dimensionful rectangular-parallelepiped body-diagonal law was found, so the faithful local interfaces above were used.
- The auxiliary prose caption says that `R₂` is the base diagonal and `R₁` is directed toward a box corner. The primary bitmap, the question's phrase “body diagonal vector `R₂`,” the stated triangle, and recorded answer C instead support `R₁` as the base diagonal and `R₂` as the body diagonal. The formalization follows the primary image as the chapter explicitly directs. The caption should be corrected in a future blueprint/source-data redraft.
- `.archon/AGENTS.md` was not present in this workspace. The available `.archon/prover-modes/physics-formalize.md` and the full user-supplied role instructions were followed.

## Verification

- `archon-lean-lsp` diagnostics: one expected `declaration uses sorry` warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0682.lean`: exit code 0 with only the expected `sorry` warning.
