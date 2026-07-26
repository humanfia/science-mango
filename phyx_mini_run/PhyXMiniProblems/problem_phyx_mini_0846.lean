import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0846

open Dimension

/-!
# Net electric flux through a cylinder in a uniform axial field

The supplied figure shows a closed circular cylinder whose axis is horizontal.
A spatially uniform electric field points from left to right, parallel to the
cylinder axis.  The diameter is labelled `2R`.  Electric-field lines enter the
left end cap, leave the right end cap, and are tangent to the curved wall.

Physical lengths, areas, field strengths, and signed electric fluxes are
represented by Physlib's unit-independent dimensionful quantities.  The
spacetime-dependent vector field itself is represented by
`Electromagnetism.ElectricField 3`.  Real numbers occur only as readouts in
specified SI units and as the numerical multiple-choice values.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L³ T⁻² C⁻¹` of electric flux, i.e. `N m² / C`. -/
def electricFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative magnitude of electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed electric flux through an oriented surface. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- SI readout of a physical area, in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- SI readout of electric-field strength, in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of signed electric flux, in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## Cylinder geometry, surface labels, and figure content -/

/-- The three pieces of the closed cylindrical Gaussian surface. -/
inductive CylinderSurfacePart where
  | leftEndCap
  | curvedWall
  | rightEndCap
  deriving DecidableEq, Repr

/-- Horizontal directions needed to transcribe the side-view figure. -/
inductive HorizontalDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/--
Typed data read directly from the supplied raster figure.  The diameter label
is a physical length; its printed text and its relation to the radius are
recorded separately below.
-/
structure UniformAxialFieldCylinderFigure where
  showsClosedCylinder : Bool
  showsSurfacePart : CylinderSurfacePart → Bool
  showsElectricFieldArrows : Bool
  electricFieldArrowDirection : HorizontalDirection
  cylinderAxisDirection : HorizontalDirection
  diameterLabel : LengthQuantity
  diameterLabelText : String

/--
An abstract closed circular cylinder in three-dimensional physical space.
`cylinderAndBoundary` identifies the spatial region on which the displayed
field is asserted to be uniform; it is not a scalar substitute for the
geometry.
-/
structure ClosedCircularCylinder where
  center : Space 3
  axisDirection : EuclideanSpace ℝ (Fin 3)
  radius : LengthQuantity
  axialLength : LengthQuantity
  endCapArea : AreaQuantity
  cylinderAndBoundary : Set (Space 3)

/--
The physical setup and its independent flux observables.  In particular,
`netElectricFlux` is not defined from the displayed answer `0`.
-/
structure UniformAxialFieldCylinderSetup where
  cylinder : ClosedCircularCylinder
  observationTime : Time
  electricField : Electromagnetism.ElectricField 3
  electricFieldStrength : ElectricFieldStrengthQuantity
  surfaceFlux : CylinderSurfacePart → ElectricFluxQuantity
  netElectricFlux : ElectricFluxQuantity
  figure : UniformAxialFieldCylinderFigure

/-! ## Figure/data readouts and governing physical laws -/

/-- Primary-image evidence, including the field direction and the `2R` label. -/
structure MatchesSuppliedCylinderFigure
    (setup : UniformAxialFieldCylinderSetup) : Prop where
  closedCylinderShown : setup.figure.showsClosedCylinder = true
  allSurfacePartsShown : ∀ part, setup.figure.showsSurfacePart part = true
  electricFieldArrowsShown : setup.figure.showsElectricFieldArrows = true
  fieldArrowsPointLeftToRight :
    setup.figure.electricFieldArrowDirection = .leftToRight
  cylinderAxisPointsLeftToRight :
    setup.figure.cylinderAxisDirection = .leftToRight
  fieldArrowsParallelToAxis :
    setup.figure.electricFieldArrowDirection =
      setup.figure.cylinderAxisDirection
  printedDiameterLabel : setup.figure.diameterLabelText = "2R"
  diameterLabelIsTwiceRadius :
    lengthInMeters setup.figure.diameterLabel =
      2 * lengthInMeters setup.cylinder.radius

/-- Regularity and circular-end geometry of the physical cylinder. -/
structure HasPhysicalClosedCylinderGeometry
    (setup : UniformAxialFieldCylinderSetup) : Prop where
  centerBelongsToCylinder :
    setup.cylinder.center ∈ setup.cylinder.cylinderAndBoundary
  axisDirectionIsUnit : ‖setup.cylinder.axisDirection‖ = 1
  radiusPositive : 0 < lengthInMeters setup.cylinder.radius
  axialLengthPositive : 0 < lengthInMeters setup.cylinder.axialLength
  circularEndCapArea :
    areaInSquareMeters setup.cylinder.endCapArea =
      Real.pi * (lengthInMeters setup.cylinder.radius) ^ 2

/--
The displayed field is uniform throughout the cylinder and parallel to its
unit axis.  PhysLean's electric field retains the vector-field role; the
dimensionful strength supplies its coherent-SI magnitude.
-/
structure IsUniformElectricFieldParallelToCylinderAxis
    (setup : UniformAxialFieldCylinderSetup) : Prop where
  strengthNonnegative :
    0 ≤ electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  fieldOnCylinder : ∀ x ∈ setup.cylinder.cylinderAndBoundary,
    setup.electricField setup.observationTime x =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength • setup.cylinder.axisDirection

/--
Orientation factor for the flux of a uniform axial field through each part of
the closed cylinder: inward at the left cap, tangent to the wall, and outward
at the right cap.
-/
def axialFluxOrientationFactor : CylinderSurfacePart → ℝ
  | .leftEndCap => -1
  | .curvedWall => 0
  | .rightEndCap => 1

/--
Surface-flux evaluation and finite additivity for the closed cylinder.  These
are the governing flux-integral laws for a uniform field parallel to the axis;
they state the three local contributions, not the requested net-zero answer.
-/
structure SatisfiesClosedCylinderElectricFluxLaws
    (setup : UniformAxialFieldCylinderSetup) : Prop where
  fluxThroughEachSurfacePart : ∀ part,
    electricFluxInNewtonSquareMetersPerCoulomb (setup.surfaceFlux part) =
      axialFluxOrientationFactor part *
        electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength *
          areaInSquareMeters setup.cylinder.endCapArea
  netFluxIsSumOfSurfaceContributions :
    electricFluxInNewtonSquareMetersPerCoulomb setup.netElectricFlux =
      electricFluxInNewtonSquareMetersPerCoulomb
          (setup.surfaceFlux .leftEndCap) +
        electricFluxInNewtonSquareMetersPerCoulomb
          (setup.surfaceFlux .curvedWall) +
        electricFluxInNewtonSquareMetersPerCoulomb
          (setup.surfaceFlux .rightEndCap)

/-! ## Multiple-choice values and target -/

/-- The answer labels printed beneath the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
Numerical answer-choice readouts in `N m² / C`; `-6/5` is the exact value
represented by the printed decimal `-1.2`.
-/
def answerChoiceFluxReadout : AnswerChoice → ℝ
  | .A => -(6 / 5)
  | .B => -10
  | .C => -2
  | .D => 0

/--
The net electric flux through the closed cylinder is zero, corresponding to
answer choice `D`.  The left and right cap contributions cancel and the field
is tangent to the curved wall.

Blueprint label: `thm:physics:phyx_mini_0846:target`.
-/
theorem netElectricFluxThroughCylinder_eq_zero
    (setup : UniformAxialFieldCylinderSetup)
    (hFigure : MatchesSuppliedCylinderFigure setup)
    (hGeometry : HasPhysicalClosedCylinderGeometry setup)
    (hField : IsUniformElectricFieldParallelToCylinderAxis setup)
    (hFluxLaws : SatisfiesClosedCylinderElectricFluxLaws setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.netElectricFlux = 0 := by
  rw [hFluxLaws.netFluxIsSumOfSurfaceContributions]
  rw [hFluxLaws.fluxThroughEachSurfacePart .leftEndCap,
    hFluxLaws.fluxThroughEachSurfacePart .curvedWall,
    hFluxLaws.fluxThroughEachSurfacePart .rightEndCap]
  simp [axialFluxOrientationFactor]

end PhyXMiniProblems.ProblemPhyXMini0846
