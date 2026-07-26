import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0851

open Dimension

/-!
# Electric flux through surface 3 of a triangular prism

The primary raster depicts a closed triangular prism whose five faces are
numbered `1` through `5`.  The prism length is labelled `4.0 m`, a transverse
height is labelled `2.0 m`, and a cross-section angle is labelled `30°`.
A uniform electric field of strength `400 N/C` points to the right, along the
prism axis.  Surface 3 is one of the prism's lateral faces and therefore
contains that axis.  Its outward area vector is normal to its tangent plane,
so the field has zero normal component and the electric flux is zero.

Lengths, electric-field vectors, oriented area vectors, and signed electric
fluxes are unit-independent Physlib `Dimensionful` quantities.  Real numbers
below are only coherent-SI readouts, dimensionless angles, or Cartesian
direction vectors.  The full uniform field also retains Physlib's
spacetime-dependent `Electromagnetism.ElectricField` type.

Assumption/target split:

* governing laws: the Physlib field is spatially and temporally uniform, field
  strength is the norm of its SI vector, oriented area vectors are normal to
  the corresponding face tangent planes, and planar flux is `E dot A`;
* previous-part results: none;
* figure/data readouts: five numbered faces of a triangular prism, surface 3
  as a lateral face, the field arrow along the prism axis and pointing right,
  `400 N/C`, `4.0 m`, `2.0 m`, and `30°`;
* current target conclusions: the flux through surface 3 is
  `0 N m^2/C`, which is displayed choice D.
-/

/-! ## Dimensionful electrostatic quantities and coherent-SI readouts -/

/-- The physical dimension `M L T^-2 C^-1` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `L^2` of an oriented surface-area vector. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- The physical dimension `M L^3 T^-2 C^-1` of electric flux. -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * areaDimension

/-- Three-dimensional Cartesian vectors used for directions and SI components. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A unit-independent physical electric-field vector. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension SpatialVector)

/-- A unit-independent oriented physical area vector. -/
abbrev AreaVectorQuantity : Type :=
  Dimensionful (WithDim areaDimension SpatialVector)

/-- A signed, unit-independent electric flux. -/
abbrev SignedElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read an electric-field strength in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read Cartesian electric-field components in newtons per coulomb. -/
def fieldVectorInNewtonsPerCoulomb
    (field : ElectricFieldVectorQuantity) : SpatialVector :=
  (field UnitChoices.SI).val

/-- Read an oriented area vector in square metres. -/
def areaVectorInSquareMeters (areaVector : AreaVectorQuantity) : SpatialVector :=
  (areaVector UnitChoices.SI).val

/-- Read signed electric flux in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : SignedElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## Five prism faces and literal primary-figure content -/

/-- The five numbered surfaces of the closed triangular prism. -/
inductive SurfaceLabel where
  | one
  | two
  | three
  | four
  | five
  deriving DecidableEq, Fintype, Repr

/-- The printed natural number associated with a surface label. -/
def SurfaceLabel.number : SurfaceLabel → ℕ
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

/-- Geometric role of a face in a triangular prism. -/
inductive PrismFaceRole where
  | triangularEnd
  | lateral
  deriving DecidableEq, Repr

/-- The role of each face identified from the primary raster. -/
def SurfaceLabel.depictedRole : SurfaceLabel → PrismFaceRole
  | .one => .triangularEnd
  | .two => .lateral
  | .three => .lateral
  | .four => .triangularEnd
  | .five => .lateral

/-- Literal visual and dimensionful label content of image `851.png`. -/
structure TriangularPrismFigure where
  showsTriangularPrism : Bool
  surfaceNumberShown : SurfaceLabel → ℕ
  fieldArrowShown : Bool
  fieldArrowPointsRight : Bool
  fieldStrengthUnitsShown : Bool
  prismLengthLabel : LengthQuantity
  transverseHeightLabel : LengthQuantity
  crossSectionAngleLabelRadians : ℝ
  fieldStrengthLabel : ElectricFieldStrengthQuantity

/-!
The physical apparatus and its independent observables.  In particular,
`electricFluxThrough` is not defined from an answer choice or from zero.
-/
structure TriangularPrismFluxSetup where
  prismLength : LengthQuantity
  transverseHeight : LengthQuantity
  crossSectionAngleRadians : ℝ
  prismAxisDirection : SpatialVector
  surfaceTangentPlane : SurfaceLabel → Submodule ℝ SpatialVector
  outwardAreaVector : SurfaceLabel → AreaVectorQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  uniformElectricFieldVector : ElectricFieldVectorQuantity
  electricField : Electromagnetism.ElectricField 3
  electricFluxThrough : SurfaceLabel → SignedElectricFluxQuantity
  figure : TriangularPrismFigure

/-! ## Figure readouts, geometry, and governing laws -/

/-!
All directly readable information from the problem and primary image.  The
angle is represented in radians, so the displayed `30°` becomes `pi / 6`.
No electric-flux value or answer choice occurs in these data.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TriangularPrismFluxSetup) : Prop where
  prismShown : setup.figure.showsTriangularPrism = true
  everySurfaceNumberShown : ∀ face,
    setup.figure.surfaceNumberShown face = face.number
  fieldArrowShown : setup.figure.fieldArrowShown = true
  fieldArrowPointsRight : setup.figure.fieldArrowPointsRight = true
  fieldUnitsAreNewtonsPerCoulomb : setup.figure.fieldStrengthUnitsShown = true
  lengthLabelIsPhysicalLength :
    setup.figure.prismLengthLabel = setup.prismLength
  heightLabelIsPhysicalHeight :
    setup.figure.transverseHeightLabel = setup.transverseHeight
  angleLabelIsPhysicalAngle :
    setup.figure.crossSectionAngleLabelRadians =
      setup.crossSectionAngleRadians
  fieldLabelIsPhysicalStrength :
    setup.figure.fieldStrengthLabel = setup.electricFieldStrength
  prismLengthMeters : lengthInMeters setup.prismLength = 4
  transverseHeightMeters : lengthInMeters setup.transverseHeight = 2
  crossSectionAngleIsThirtyDegrees :
    setup.crossSectionAngleRadians = Real.pi / 6
  fieldStrengthNewtonsPerCoulomb :
    fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength = 400

/-!
Coordinate-free triangular-prism geometry.  A lateral face contains the
prism axis, while each outward area vector spans a line orthogonal to its
face tangent plane.  This states geometry for every face rather than the
requested flux value for face 3.
-/
structure SatisfiesTriangularPrismGeometry
    (setup : TriangularPrismFluxSetup) : Prop where
  axisDirectionIsUnit : ‖setup.prismAxisDirection‖ = 1
  everyLateralFaceContainsAxis : ∀ face,
    face.depictedRole = .lateral →
      setup.prismAxisDirection ∈ setup.surfaceTangentPlane face
  everyAreaVectorIsNonzero : ∀ face,
    areaVectorInSquareMeters (setup.outwardAreaVector face) ≠ 0
  areaVectorNormalToFace : ∀ face,
    Submodule.IsOrtho
      (setup.surfaceTangentPlane face)
      (Submodule.span ℝ
        {areaVectorInSquareMeters (setup.outwardAreaVector face)})

/-!
The arrows in the raster show the electric field parallel to the prism axis
and in its positive direction.  The positive scalar is not fixed to a target
flux and the field vector itself remains an independent physical quantity.
-/
structure ElectricFieldAlignedWithPrismAxis
    (setup : TriangularPrismFluxSetup) : Prop where
  positiveMultipleOfAxis : ∃ magnitude : ℝ,
    0 < magnitude ∧
      fieldVectorInNewtonsPerCoulomb setup.uniformElectricFieldVector =
        magnitude • setup.prismAxisDirection

/-!
The unit-aware vector calibrates Physlib's electric field at every spacetime
point, and its norm calibrates the independent physical strength.
-/
structure SatisfiesUniformElectricFieldModel
    (setup : TriangularPrismFluxSetup) : Prop where
  uniformAtEveryEvent : ∀ time position,
    setup.electricField time position =
      fieldVectorInNewtonsPerCoulomb setup.uniformElectricFieldVector
  strengthIsVectorNorm :
    fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength =
      ‖fieldVectorInNewtonsPerCoulomb setup.uniformElectricFieldVector‖

/-!
The planar, uniform-field flux law `Phi = E dot A`, imposed on every face of
the prism.  This governing law does not single out surface 3 or assert zero.
-/
structure SatisfiesPlanarElectricFluxLaw
    (setup : TriangularPrismFluxSetup) : Prop where
  fluxEqualsFieldDotArea : ∀ face,
    electricFluxInNewtonSquareMetersPerCoulomb
        (setup.electricFluxThrough face) =
      inner ℝ
        (fieldVectorInNewtonsPerCoulomb setup.uniformElectricFieldVector)
        (areaVectorInSquareMeters (setup.outwardAreaVector face))

/-! ## Displayed choices and formalized conclusions -/

/-- Labels of the four electric-flux choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed flux in `N m^2/C` associated with each answer choice. -/
def answerFluxInNewtonSquareMetersPerCoulomb : AnswerChoice → ℝ
  | .A => 80
  | .B => 10
  | .C => 20
  | .D => 0

/-- The answer label recorded by the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Because surface 3 is lateral and the depicted field is axial, its field
vector belongs to the surface-3 tangent plane.  This is a geometric
intermediate result and does not mention electric flux.
-/
lemma fieldVector_mem_surfaceThreeTangentPlane
    (setup : TriangularPrismFluxSetup)
    (hGeometry : SatisfiesTriangularPrismGeometry setup)
    (hAlignment : ElectricFieldAlignedWithPrismAxis setup) :
    fieldVectorInNewtonsPerCoulomb setup.uniformElectricFieldVector ∈
      setup.surfaceTangentPlane .three := by
  rcases hAlignment.positiveMultipleOfAxis with ⟨magnitude, _, hField⟩
  rw [hField]
  exact (setup.surfaceTangentPlane .three).smul_mem magnitude
    (hGeometry.everyLateralFaceContainsAxis .three rfl)

/-!
The tangent field is orthogonal to surface 3's outward area vector, so the
planar flux law gives zero signed electric flux.
-/
lemma electricFluxThroughSurfaceThree_eq_zero
    (setup : TriangularPrismFluxSetup)
    (hGeometry : SatisfiesTriangularPrismGeometry setup)
    (hAlignment : ElectricFieldAlignedWithPrismAxis setup)
    (hFluxLaw : SatisfiesPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb
        (setup.electricFluxThrough .three) = 0 := by
  rw [hFluxLaw.fluxEqualsFieldDotArea]
  exact (hGeometry.areaVectorNormalToFace .three).inner_eq
    (fieldVector_mem_surfaceThreeTangentPlane setup hGeometry hAlignment)
    (Submodule.mem_span_singleton_self _)

/-!
For the depicted uniform `400 N/C` field, surface 3 is parallel to the field,
so its electric flux is `0 N m^2/C`, the value printed as answer D.

This declaration formalizes `thm:physics:phyx_mini_0851:target`.  Neither the
zero flux nor its agreement with answer D appears in any premise, setup field,
or governing-law field.
-/
theorem problem_phyx_mini_0851
    (setup : TriangularPrismFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hGeometry : SatisfiesTriangularPrismGeometry setup)
    (hAlignment : ElectricFieldAlignedWithPrismAxis setup)
    (hUniformField : SatisfiesUniformElectricFieldModel setup)
    (hFluxLaw : SatisfiesPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb
          (setup.electricFluxThrough .three) = 0 ∧
      electricFluxInNewtonSquareMetersPerCoulomb
          (setup.electricFluxThrough .three) =
        answerFluxInNewtonSquareMetersPerCoulomb
          recordedDatasetAnswer := by
  have hZero :=
    electricFluxThroughSurfaceThree_eq_zero setup hGeometry hAlignment hFluxLaw
  constructor
  · exact hZero
  · simpa [recordedDatasetAnswer, answerFluxInNewtonSquareMetersPerCoulomb] using hZero

end PhyXMiniProblems.ProblemPhyXMini0851
