import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Physlib.SpaceAndTime.Space.CrossProduct

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0792

open Matrix Space

/-!
# Cross product of two vectors in the `xy`-plane

The components below are numerical readouts in the common, unspecified vector
unit used by the problem.  Consequently, the components of the cross product
are readouts in the square of that unit.  The problem does not identify the
vectors as displacements, forces, or another more specific dimensionful
quantity, so no such physical role is imposed here.

The supplied raster fixes the orientation: `A` lies along `+x`, while `B` is
rotated from `A` toward `+y` through `30°`.  The drawn `C` arrow is retained as
uncalibrated figure metadata; its direction or magnitude is not assumed for the
unknown vector-product readout.
-/

/-! ## Three-dimensional vector operations -/

/-- Numerical Cartesian components of a three-dimensional spatial vector. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- The three labelled coordinate axes in the supplied raster. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index belonging to a labelled axis. -/
def axisIndex : CoordinateAxis → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

/-- Unit vector along a labelled positive coordinate axis. -/
def axisVector (axis : CoordinateAxis) : SpatialVector :=
  EuclideanSpace.single (axisIndex axis) 1

/-- Unit vector `i-hat` along `+x`. -/
def iHat : SpatialVector := axisVector .x

/-- Unit vector `j-hat` along `+y`. -/
def jHat : SpatialVector := axisVector .y

/-- Unit vector `k-hat` along `+z`. -/
def kHat : SpatialVector := axisVector .z

/-- The three coordinate planes determined by the labelled axes. -/
inductive CoordinatePlane where
  | xy
  | yz
  | zx
  deriving DecidableEq, Repr

/-- A vector has zero component normal to the indicated coordinate plane. -/
def LiesInCoordinatePlane
    (vector : SpatialVector) : CoordinatePlane → Prop
  | .xy => vector (axisIndex .z) = 0
  | .yz => vector (axisIndex .x) = 0
  | .zx => vector (axisIndex .y) = 0

/-- A nonzero vector is a positive scalar multiple of a labelled axis. -/
def PointsAlongPositiveAxis
    (vector : SpatialVector) (axis : CoordinateAxis) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧ vector = magnitude • axisVector axis

/-! ## Physical setup and primary-raster vocabulary -/

/-- Vector labels printed beside the three arrows in image `792.png`. -/
inductive FigureVectorLabel where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- Positive or negative sense along a labelled coordinate axis. -/
inductive AxisSense where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Literal and qualitative information visible in the supplied raster. -/
structure VectorProductFigure where
  coordinateAxisShown : CoordinateAxis → Bool
  vectorLabelShown : FigureVectorLabel → Bool
  originLabelShown : Bool
  shadedPlane : CoordinatePlane
  markedAngleDegrees : ℝ
  cArrowAxis : CoordinateAxis
  cArrowSense : AxisSense
  bIsCounterclockwiseFromAInXYView : Bool
  hasCalibratedMetricScale : Bool

/-!
The three vectors are independent data.  In particular, `vectorCInSquaredUnits`
is not defined to be either a cross product or an answer choice; the governing
cross-product relation is an explicit law below.
-/
structure VectorProductSetup where
  /-- Cartesian readout of `A` in the problem's common vector unit. -/
  vectorAInUnits : SpatialVector
  /-- Cartesian readout of `B` in the same vector unit. -/
  vectorBInUnits : SpatialVector
  /-- Unknown Cartesian readout of `C` in the square of that unit. -/
  vectorCInSquaredUnits : SpatialVector
  /-- The dimensionless angle from `A` to `B`, represented in radians. -/
  phiRadians : ℝ
  figure : VectorProductFigure

/-! ## Assumptions from the prose and figure -/

/-- Quantitative and geometric data stated in the problem prose. -/
structure StatedVectorData (setup : VectorProductSetup) : Prop where
  vectorAMagnitude : ‖setup.vectorAInUnits‖ = 6
  vectorAPointsAlongPositiveX :
    PointsAlongPositiveAxis setup.vectorAInUnits .x
  vectorBMagnitude : ‖setup.vectorBInUnits‖ = 4
  vectorBLiesInXYPlane :
    LiesInCoordinatePlane setup.vectorBInUnits .xy
  angleFromAToB :
    InnerProductGeometry.angle
      setup.vectorAInUnits setup.vectorBInUnits = setup.phiRadians

/-!
Image-derived facts.  The positive `y` component disambiguates the two planar
vectors making the same undirected angle with `+x`.  No calibrated numerical
fact about the drawn `C` arrow is asserted.
-/
structure MatchesSuppliedFigure (setup : VectorProductSetup) : Prop where
  everyAxisIsShown : ∀ axis, setup.figure.coordinateAxisShown axis = true
  everyVectorLabelIsShown :
    ∀ label, setup.figure.vectorLabelShown label = true
  originOIsShown : setup.figure.originLabelShown = true
  shadedPlaneIsXY : setup.figure.shadedPlane = .xy
  angleMarkIsThirtyDegrees : setup.figure.markedAngleDegrees = 30
  angleMarkMatchesRadians :
    setup.phiRadians = setup.figure.markedAngleDegrees * Real.pi / 180
  vectorBHasPositiveYComponent :
    0 < setup.vectorBInUnits (axisIndex .y)
  vectorBIsShownCounterclockwiseFromA :
    setup.figure.bIsCounterclockwiseFromAInXYView = true
  cArrowIsDrawnOnZAxis : setup.figure.cArrowAxis = .z
  cArrowIsDrawnInPositiveSense : setup.figure.cArrowSense = .positive
  rasterHasNoCalibratedMetricScale :
    setup.figure.hasCalibratedMetricScale = false

/-- Governing relation specified by `C = A × B`. -/
structure SatisfiesVectorProductLaw (setup : VectorProductSetup) : Prop where
  resultIsCrossProduct :
    setup.vectorCInSquaredUnits =
      setup.vectorAInUnits ⨯ₑ₃ setup.vectorBInUnits

/-! ## Displayed multiple-choice data -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical coefficient of `k-hat` printed in an answer choice. -/
def displayedCoefficient : AnswerChoice → ℝ
  | .A => 15
  | .B => 12
  | .C => 8
  | .D => 18

/-- Vector printed by an answer choice, in squared vector units. -/
def displayedAnswerVector (choice : AnswerChoice) : SpatialVector :=
  displayedCoefficient choice • kHat

/-!
The vector product has magnitude `6 * 4 * sin 30° = 12`; the orientation read
from `A` toward `B` and the right-hand rule give the positive `z` direction.
Thus this is the vector printed as answer choice B.
-/
theorem vectorProduct_eq_twelve_kHat
    (setup : VectorProductSetup)
    (data : StatedVectorData setup)
    (figureData : MatchesSuppliedFigure setup)
    (law : SatisfiesVectorProductLaw setup) :
    setup.vectorCInSquaredUnits = (12 : ℝ) • kHat := by
  rcases data.vectorAPointsAlongPositiveX with ⟨m, hm, hA⟩
  have hAmag := data.vectorAMagnitude
  simp [hA, axisVector, axisIndex, norm_smul, abs_of_pos hm] at hAmag
  subst m
  have hphi : setup.phiRadians = Real.pi / 6 := by
    rw [figureData.angleMarkMatchesRadians, figureData.angleMarkIsThirtyDegrees]
    ring
  have hinner := InnerProductGeometry.cos_angle_mul_norm_mul_norm
    setup.vectorAInUnits setup.vectorBInUnits
  rw [data.angleFromAToB, hphi, data.vectorAMagnitude, data.vectorBMagnitude,
    Real.cos_pi_div_six] at hinner
  simp [hA, axisVector, axisIndex, EuclideanSpace.inner_eq_star_dotProduct] at hinner
  ring_nf at hinner
  have hBx : setup.vectorBInUnits (axisIndex .x) = 2 * Real.sqrt 3 := by
    simp [axisIndex]
    nlinarith [hinner]
  have hBnormSq := EuclideanSpace.real_norm_sq_eq setup.vectorBInUnits
  rw [data.vectorBMagnitude] at hBnormSq
  norm_num [Fin.sum_univ_succ] at hBnormSq
  change 16 = setup.vectorBInUnits 0 ^ 2 +
    (setup.vectorBInUnits 1 ^ 2 + setup.vectorBInUnits 2 ^ 2) at hBnormSq
  have hBz : setup.vectorBInUnits (2 : Fin 3) = 0 := by
    simpa [LiesInCoordinatePlane, axisIndex] using data.vectorBLiesInXYPlane
  have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hBy : setup.vectorBInUnits (axisIndex .y) = 2 := by
    have hBx0 : setup.vectorBInUnits (0 : Fin 3) = 2 * Real.sqrt 3 := by
      simpa [axisIndex] using hBx
    have hByPos : 0 < setup.vectorBInUnits (1 : Fin 3) := by
      simpa [axisIndex] using figureData.vectorBHasPositiveYComponent
    change setup.vectorBInUnits (1 : Fin 3) = 2
    rw [hBx0, hBz] at hBnormSq
    nlinarith
  simp [axisIndex] at hBy
  rw [law.resultIsCrossProduct, hA]
  ext i
  fin_cases i <;>
    simp [axisVector, axisIndex, kHat, cross_apply, hBy, hBz]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0792
