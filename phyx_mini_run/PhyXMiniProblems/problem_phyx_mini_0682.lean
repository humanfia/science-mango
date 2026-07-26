import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Units.WithDim.Basic

/-!
# Body diagonal of a rectangular parallelepiped

The primary figure labels the mutually perpendicular edge lengths by `a`, `b`,
and `c` along the `x`, `y`, and `z` axes.  The arrow `R₁` is the diagonal of
the `xy` base face.  Together, `R₁`, the vertical edge `c k̂`, and the arrow
`R₂` form the shaded right triangle, with `R₂` the body diagonal.

Edge lengths and displacement vectors are Physlib dimensionful quantities.
Their values in any coherent choice of units are respectively real scalars
and vectors in three-dimensional Euclidean space.  Thus the unit-vector
expression in the conclusion is required in every unit system, rather than
only for one untyped scalar representation.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0682

open Dimension

/-! ## Dimensionful quantities and Cartesian unit vectors -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A dimensionful spatial displacement with three signed Cartesian components. -/
abbrev SpatialDisplacement : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 3)))

/-- The scalar readout of a physical length in a coherent unit system. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- The Cartesian readout of a physical displacement in a coherent unit system. -/
def displacementReadout
    (units : UnitChoices) (displacement : SpatialDisplacement) :
    EuclideanSpace ℝ (Fin 3) :=
  (displacement units).val

/-- The dimensionless Cartesian unit vector `î` along the `x` axis. -/
def iHat : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- The dimensionless Cartesian unit vector `ĵ` along the `y` axis. -/
def jHat : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- The dimensionless Cartesian unit vector `k̂` along the `z` axis. -/
def kHat : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (2 : Fin 3) 1

/-! ## Labels and qualitative information from the supplied figure -/

/-- The three coordinate axes printed in the figure. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

/-- The three dimension labels printed on the box. -/
inductive DimensionLabel where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The two named vector arrows in the figure. -/
inductive FigureVectorLabel where
  | R1
  | R2
  deriving DecidableEq, Repr

/-- Geometrically distinguished points needed to describe the two arrows. -/
inductive FigurePointLabel where
  | originO
  | baseOppositeCorner
  | bodyOppositeCorner
  deriving DecidableEq, Repr

/-- The geometric role assigned to each named vector arrow. -/
inductive VectorRole where
  | baseFaceDiagonal
  | bodyDiagonal
  deriving DecidableEq, Repr

/--
Qualitative labels and marks visible in the primary bitmap.  These fields do
not impose any component formula on either physical displacement.
-/
structure SuppliedParallelepipedFigure where
  dimensionAxis : DimensionLabel → CoordinateAxis
  vectorRole : FigureVectorLabel → VectorRole
  arrowStart : FigureVectorLabel → FigurePointLabel
  arrowEnd : FigureVectorLabel → FigurePointLabel
  showsRectangularParallelepiped : Bool
  showsXAxisLabel : Bool
  showsYAxisLabel : Bool
  showsZAxisLabel : Bool
  showsShadedR1CkR2Triangle : Bool

/--
The three physical edge lengths and two physical displacement vectors named
in the problem, together with the supplied diagram.
-/
structure RectangularParallelepipedSetup where
  edgeLength : DimensionLabel → LengthQuantity
  displacement : FigureVectorLabel → SpatialDisplacement
  figure : SuppliedParallelepipedFigure

/-! ## Figure readouts, physical branch, and governing geometry -/

/--
The axis assignments and arrow roles read from the primary figure.  In
particular, this identifies `R₁` as the base diagonal and `R₂` as the body
diagonal, without assuming the requested component expression for `R₂`.
-/
structure MatchesSuppliedFigure
    (setup : RectangularParallelepipedSetup) : Prop where
  boxIsRectangular : setup.figure.showsRectangularParallelepiped = true
  xAxisShown : setup.figure.showsXAxisLabel = true
  yAxisShown : setup.figure.showsYAxisLabel = true
  zAxisShown : setup.figure.showsZAxisLabel = true
  dimensionAAlongX : setup.figure.dimensionAxis .a = .x
  dimensionBAlongY : setup.figure.dimensionAxis .b = .y
  dimensionCAlongZ : setup.figure.dimensionAxis .c = .z
  rOneIsBaseDiagonal : setup.figure.vectorRole .R1 = .baseFaceDiagonal
  rTwoIsBodyDiagonal : setup.figure.vectorRole .R2 = .bodyDiagonal
  rOneStartsAtO : setup.figure.arrowStart .R1 = .originO
  rTwoStartsAtO : setup.figure.arrowStart .R2 = .originO
  rOneEndsAtBaseCorner :
    setup.figure.arrowEnd .R1 = .baseOppositeCorner
  rTwoEndsAtBodyCorner :
    setup.figure.arrowEnd .R2 = .bodyOppositeCorner
  rightTriangleShown : setup.figure.showsShadedR1CkR2Triangle = true

/-- The physical branch in which all three edge dimensions are nonzero. -/
structure HasPositiveEdgeLengths
    (setup : RectangularParallelepipedSetup) : Prop where
  positiveInSI :
    ∀ label : DimensionLabel,
      0 < lengthReadout UnitChoices.SI (setup.edgeLength label)

/--
Vector addition across the rectangular `xy` base face: its diagonal `R₁` is
the sum of the `a` edge along `î` and the `b` edge along `ĵ`.
-/
structure SatisfiesBaseFaceDiagonalGeometry
    (setup : RectangularParallelepipedSetup) : Prop where
  rOneComponents :
    ∀ units : UnitChoices,
      displacementReadout units (setup.displacement .R1) =
        lengthReadout units (setup.edgeLength .a) • iHat +
          lengthReadout units (setup.edgeLength .b) • jHat

/--
The stated right-triangle law.  Traversing `R₁` and then the vertical edge
`c k̂` gives `R₂`; the base diagonal is perpendicular to that vertical leg.
Neither field contains the requested three-component expansion of `R₂`.
-/
structure SatisfiesBodyDiagonalRightTriangle
    (setup : RectangularParallelepipedSetup) : Prop where
  displacementComposition :
    ∀ units : UnitChoices,
      displacementReadout units (setup.displacement .R2) =
        displacementReadout units (setup.displacement .R1) +
          lengthReadout units (setup.edgeLength .c) • kHat
  legsPerpendicular :
    ∀ units : UnitChoices,
      inner ℝ
          (displacementReadout units (setup.displacement .R1))
          (lengthReadout units (setup.edgeLength .c) • kHat) = 0

/-! ## Displayed answers and target -/

/-- Labels of the four displayed multiple-choice expressions. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The vector expression printed beside each answer choice. -/
def displayedBodyDiagonalReadout
    (setup : RectangularParallelepipedSetup) (units : UnitChoices) :
    AnswerChoice → EuclideanSpace ℝ (Fin 3)
  | .A =>
      lengthReadout units (setup.edgeLength .c) • iHat +
        lengthReadout units (setup.edgeLength .b) • jHat +
          lengthReadout units (setup.edgeLength .b) • kHat
  | .B =>
      lengthReadout units (setup.edgeLength .b) • iHat +
        lengthReadout units (setup.edgeLength .a) • jHat +
          lengthReadout units (setup.edgeLength .c) • kHat
  | .C =>
      lengthReadout units (setup.edgeLength .a) • iHat +
        lengthReadout units (setup.edgeLength .b) • jHat +
          lengthReadout units (setup.edgeLength .c) • kHat
  | .D =>
      lengthReadout units (setup.edgeLength .a) • iHat +
        lengthReadout units (setup.edgeLength .c) • jHat +
          lengthReadout units (setup.edgeLength .b) • kHat

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed expression agrees with the physical body diagonal in all units. -/
def MatchesDisplayedBodyDiagonal
    (setup : RectangularParallelepipedSetup) (choice : AnswerChoice) : Prop :=
  ∀ units : UnitChoices,
    displacementReadout units (setup.displacement .R2) =
      displayedBodyDiagonalReadout setup units choice

/--
The body diagonal is
`R₂ = a î + b ĵ + c k̂` in every coherent unit system, hence it agrees
with displayed answer C.

Blueprint: `thm:physics:phyx_mini_0682:target`.
-/
theorem problem_phyx_mini_0682
    (setup : RectangularParallelepipedSetup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPositiveEdgeLengths setup)
    (_baseGeometry : SatisfiesBaseFaceDiagonalGeometry setup)
    (_bodyTriangle : SatisfiesBodyDiagonalRightTriangle setup) :
    (∀ units : UnitChoices,
      displacementReadout units (setup.displacement .R2) =
        lengthReadout units (setup.edgeLength .a) • iHat +
          lengthReadout units (setup.edgeLength .b) • jHat +
            lengthReadout units (setup.edgeLength .c) • kHat) ∧
      MatchesDisplayedBodyDiagonal setup .C := by
  have hcomponents : ∀ units : UnitChoices,
      displacementReadout units (setup.displacement .R2) =
        lengthReadout units (setup.edgeLength .a) • iHat +
          lengthReadout units (setup.edgeLength .b) • jHat +
            lengthReadout units (setup.edgeLength .c) • kHat := by
    intro units
    rw [_bodyTriangle.displacementComposition units,
      _baseGeometry.rOneComponents units]
  exact ⟨hcomponents, by
    simpa [MatchesDisplayedBodyDiagonal, displayedBodyDiagonalReadout] using
      hcomponents⟩

end PhyXMiniProblems.ProblemPhyXMini0682
