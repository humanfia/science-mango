import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0952

open Dimension

/-!
# Force on a square current loop in a nonuniform magnetic field

The square loop lies in the `xy`-plane, with coherent-SI corner coordinates
`(0,0)`, `(0,L)`, `(L,L)`, and `(L,0)`. Its current follows the left, top,
right, and bottom sides in that order, hence clockwise. At the observation
time, the magnetic field is

`B(x,y,z) = (B₀ z / L) e_y + (B₀ y / L) e_z`.

Dimensionful physical quantities are kept distinct from their coherent-SI
readouts. In particular, the four side forces and net force are independent
observables constrained by the magnetic wire-force law; none is defined to
be the requested result.
-/

/-! ## Physical dimensions, quantities, and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Magnetic flux density has the tesla dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Force has the newton dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A coherent-SI three-dimensional vector readout. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A unit-independent signed three-dimensional force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  coherentSIReadout length

/-- Read a current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  coherentSIReadout current

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityMagnitude) : ℝ :=
  coherentSIReadout density

/-- Read a physical force vector in newtons. -/
def forceVectorInNewtons (force : ForceVectorQuantity) : SpatialVector :=
  (force UnitChoices.SI).val

/-! ## Cartesian geometry and primary-figure vocabulary -/

/-- Cartesian axes, including the normal to the plane of the loop. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Standard coherent-SI unit vector associated with an axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- The ordinary right-handed cross product on coherent-SI spatial vectors. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- The four labelled vertices of the square in the supplied image. -/
inductive LoopVertex where
  | lowerLeft
  | upperLeft
  | upperRight
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- The four sides, named by their position in the supplied image. -/
inductive LoopSide where
  | left
  | top
  | right
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- Symbolic coordinate labels printed next to the four vertices. -/
inductive VertexCoordinateLabel where
  | zeroZero
  | zeroL
  | LL
  | LZero
  deriving DecidableEq, Fintype, Repr

/-- Six oriented Cartesian directions used for arrows and force directions. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  | positiveZ
  | negativeZ
  deriving DecidableEq, Fintype, Repr

/-- Unit vector representing an oriented Cartesian direction. -/
def axisDirectionVector : AxisDirection → SpatialVector
  | .positiveX => axisVector .x
  | .negativeX => -axisVector .x
  | .positiveY => axisVector .y
  | .negativeY => -axisVector .y
  | .positiveZ => axisVector .z
  | .negativeZ => -axisVector .z

/-- A nonzero vector points in an axis direction when it is a positive
multiple of the corresponding oriented unit vector. -/
def PointsInAxisDirection
    (vector : SpatialVector) (direction : AxisDirection) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    vector = magnitude • axisDirectionVector direction

/-- Plane in which the wire loop is placed. -/
inductive CoordinatePlane where
  | xy
  | yz
  | zx
  deriving DecidableEq, Repr

/-- Shape classification of the closed wire loop. -/
inductive LoopShape where
  | square
  | other
  deriving DecidableEq, Repr

/-- Orientation of the current around the closed loop. -/
inductive LoopCurrentOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Time dependence of the current magnitude. -/
inductive CurrentRegime where
  | constant
  | timeVarying
  deriving DecidableEq, Repr

/-- Colours distinguished for the arrows in the primary raster. -/
inductive FigureColor where
  | purple
  | other
  deriving DecidableEq, Repr

/-- Literal labels and arrows visible in the primary image `952.png`. -/
structure SquareLoopFigure where
  axisShown : CoordinateAxis → Bool
  vertexShown : LoopVertex → Bool
  vertexCoordinateLabel : LoopVertex → VertexCoordinateLabel
  currentArrowShown : LoopSide → Bool
  currentArrowDirection : LoopSide → AxisDirection
  currentArrowColor : FigureColor

/-- The vertex at which the current-directed parametrization of a side starts. -/
def sideStartVertex : LoopSide → LoopVertex
  | .left => .lowerLeft
  | .top => .upperLeft
  | .right => .upperRight
  | .bottom => .lowerRight

/-- The vertex at which the current-directed parametrization of a side ends. -/
def sideEndVertex : LoopSide → LoopVertex
  | .left => .upperLeft
  | .top => .upperRight
  | .right => .lowerRight
  | .bottom => .lowerLeft

/-- Coherent-SI vector with the coordinates of a labelled vertex. -/
def vertexVectorInMeters
    (sideLengthMeters : ℝ) : LoopVertex → SpatialVector
  | .lowerLeft => 0
  | .upperLeft => sideLengthMeters • axisVector .y
  | .upperRight =>
      sideLengthMeters • axisVector .x +
        sideLengthMeters • axisVector .y
  | .lowerRight => sideLengthMeters • axisVector .x

/-- Current-directed displacement along one complete side, in metres. -/
def sideDisplacementInMeters
    (sideLengthMeters : ℝ) : LoopSide → SpatialVector
  | .left => sideLengthMeters • axisVector .y
  | .top => sideLengthMeters • axisVector .x
  | .right => (-sideLengthMeters) • axisVector .y
  | .bottom => (-sideLengthMeters) • axisVector .x

/-- Affine current-directed parametrization of a side for `u ∈ [0,1]`. -/
def squareSidePointInMeters
    (sideLengthMeters : ℝ) (side : LoopSide) (u : ℝ) : SpatialVector :=
  vertexVectorInMeters sideLengthMeters (sideStartVertex side) +
    u • sideDisplacementInMeters sideLengthMeters side

/-- Interpret a coherent-SI metre coordinate vector as a Physlib space point. -/
def spacePointOfMeters (vector : SpatialVector) : Space 3 :=
  ⟨vector.ofLp⟩

/-! ## Physical setup, figure evidence, and geometry -/

/--
Independent physical objects and observables. The Physlib magnetic field is
a spacetime-dependent vector field. The side and net forces are independent
dimensionful quantities, not definitions of their expected values.
-/
structure SquareCurrentLoopSetup where
  loopShape : LoopShape
  loopPlane : CoordinatePlane
  currentRegime : CurrentRegime
  currentOrientation : LoopCurrentOrientation
  sideLength : LengthQuantity
  currentMagnitude : ElectricCurrentMagnitude
  fieldScale : MagneticFluxDensityMagnitude
  observationTime : Time
  magneticField : Electromagnetism.MagneticField 3
  vertexPosition : LoopVertex → Space 3
  wirePath : LoopSide → ℝ → Space 3
  wireTangentInMeters : LoopSide → SpatialVector
  sideMagneticForce : LoopSide → ForceVectorQuantity
  netMagneticForce : ForceVectorQuantity
  figure : SquareLoopFigure

/-- Qualitative setup stated in the written problem. -/
structure MatchesWrittenSquareLoopScenario
    (setup : SquareCurrentLoopSetup) : Prop where
  loopIsSquare : setup.loopShape = .square
  loopLiesInXYPlane : setup.loopPlane = .xy
  currentIsConstant : setup.currentRegime = .constant
  currentIsClockwise : setup.currentOrientation = .clockwise

/-- Literal axis, coordinate-label, colour, and current-arrow evidence in
the supplied image. This structure contains no force information. -/
structure MatchesSuppliedSquareLoopFigure
    (setup : SquareCurrentLoopSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisNotShown : setup.figure.axisShown .z = false
  everyVertexShown : ∀ vertex, setup.figure.vertexShown vertex = true
  lowerLeftLabel :
    setup.figure.vertexCoordinateLabel .lowerLeft = .zeroZero
  upperLeftLabel :
    setup.figure.vertexCoordinateLabel .upperLeft = .zeroL
  upperRightLabel :
    setup.figure.vertexCoordinateLabel .upperRight = .LL
  lowerRightLabel :
    setup.figure.vertexCoordinateLabel .lowerRight = .LZero
  everyCurrentArrowShown : ∀ side,
    setup.figure.currentArrowShown side = true
  leftArrowPointsUp :
    setup.figure.currentArrowDirection .left = .positiveY
  topArrowPointsRight :
    setup.figure.currentArrowDirection .top = .positiveX
  rightArrowPointsDown :
    setup.figure.currentArrowDirection .right = .negativeY
  bottomArrowPointsLeft :
    setup.figure.currentArrowDirection .bottom = .negativeX
  currentArrowsArePurple : setup.figure.currentArrowColor = .purple

/-- The metric interpretation of the four symbolic corner labels and the
clockwise side parametrizations. -/
structure HasDepictedSquareLoopGeometry
    (setup : SquareCurrentLoopSetup) : Prop where
  vertexCoordinates : ∀ vertex,
    setup.vertexPosition vertex =
      spacePointOfMeters
        (vertexVectorInMeters (lengthInMeters setup.sideLength) vertex)
  currentDirectedSidePaths : ∀ side u,
    setup.wirePath side u =
      spacePointOfMeters
        (squareSidePointInMeters
          (lengthInMeters setup.sideLength) side u)
  currentDirectedTangents : ∀ side,
    setup.wireTangentInMeters side =
      sideDisplacementInMeters (lengthInMeters setup.sideLength) side

/-- Positivity and nondegeneracy implicit in a genuine current-carrying loop
and in the statement that `B₀` is positive. -/
structure HasPhysicalLoopParameters
    (setup : SquareCurrentLoopSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  currentMagnitudePositive : 0 < currentInAmperes setup.currentMagnitude
  fieldScalePositive :
    0 < magneticFluxDensityInTeslas setup.fieldScale

/-! ## Specified field and governing magnetic-force law -/

/-- At the observation time the field has no `x` component and obeys
`B(x,y,z) = (B₀ z / L) e_y + (B₀ y / L) e_z`. This is given field data,
not a statement about the requested force. -/
structure HasSpecifiedNonuniformMagneticField
    (setup : SquareCurrentLoopSetup) : Prop where
  fieldFormula : ∀ position : Space 3,
    setup.magneticField setup.observationTime position =
      (magneticFluxDensityInTeslas setup.fieldScale * position.val (2 : Fin 3) /
          lengthInMeters setup.sideLength) • axisVector .y +
      (magneticFluxDensityInTeslas setup.fieldScale * position.val (1 : Fin 3) /
          lengthInMeters setup.sideLength) • axisVector .z

/-- The general magnetic force law `dF = I (dℓ × B)`, integrated separately
over each current-directed side, together with additivity of the four side
forces. It contains no asserted value or direction for the net force. -/
structure SatisfiesMagneticWireForceLaw
    (setup : SquareCurrentLoopSetup) : Prop where
  sideForceLineIntegral : ∀ side,
    forceVectorInNewtons (setup.sideMagneticForce side) =
      currentInAmperes setup.currentMagnitude •
        (∫ u in (0 : ℝ)..1,
          spatialCross (setup.wireTangentInMeters side)
            (setup.magneticField setup.observationTime
              (setup.wirePath side u)))
  netForceIsSumOfSideForces :
    forceVectorInNewtons setup.netMagneticForce =
      ∑ side : LoopSide,
        forceVectorInNewtons (setup.sideMagneticForce side)

/-! ## Derived side forces, answer metadata, and requested result -/

/-- The forces derived on the left, top, right, and bottom sides. In
particular, the horizontal forces from the vertical sides cancel, the top
side supplies the full negative-`y` contribution, and the bottom contribution
vanishes because it lies at `y = 0`. -/
lemma force_on_each_side
    (setup : SquareCurrentLoopSetup)
    (hGeometry : HasDepictedSquareLoopGeometry setup)
    (hField : HasSpecifiedNonuniformMagneticField setup)
    (hLaws : SatisfiesMagneticWireForceLaw setup) :
    forceVectorInNewtons (setup.sideMagneticForce .left) =
        (currentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas setup.fieldScale *
            lengthInMeters setup.sideLength / 2) • axisVector .x ∧
      forceVectorInNewtons (setup.sideMagneticForce .top) =
        (-(currentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas setup.fieldScale *
            lengthInMeters setup.sideLength)) • axisVector .y ∧
      forceVectorInNewtons (setup.sideMagneticForce .right) =
        (-(currentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas setup.fieldScale *
            lengthInMeters setup.sideLength / 2)) • axisVector .x ∧
      forceVectorInNewtons (setup.sideMagneticForce .bottom) = 0 := by
  by_cases hL : lengthInMeters setup.sideLength = 0
  · have hIntegrand (side : LoopSide) (u : ℝ) :
        spatialCross
            (sideDisplacementInMeters (lengthInMeters setup.sideLength) side)
            ((magneticFluxDensityInTeslas setup.fieldScale *
                    (spacePointOfMeters (squareSidePointInMeters
                      (lengthInMeters setup.sideLength) side u)).val (2 : Fin 3) /
                  lengthInMeters setup.sideLength) • axisVector .y +
              (magneticFluxDensityInTeslas setup.fieldScale *
                    (spacePointOfMeters (squareSidePointInMeters
                      (lengthInMeters setup.sideLength) side u)).val (1 : Fin 3) /
                  lengthInMeters setup.sideLength) • axisVector .z) =
          match side with
          | .left =>
              (magneticFluxDensityInTeslas setup.fieldScale * u *
                lengthInMeters setup.sideLength) • axisVector .x
          | .top =>
              (-(magneticFluxDensityInTeslas setup.fieldScale *
                lengthInMeters setup.sideLength)) • axisVector .y
          | .right =>
              (-(magneticFluxDensityInTeslas setup.fieldScale * (1 - u) *
                lengthInMeters setup.sideLength)) • axisVector .x
          | .bottom => 0 := by
      cases side <;>
        simp [hL, spatialCross, sideDisplacementInMeters]
    constructor
    · rw [hLaws.sideForceLineIntegral]
      simp only [hGeometry.currentDirectedTangents,
        hGeometry.currentDirectedSidePaths, hField.fieldFormula]
      rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .left u)]
      simp [hL]
    · constructor
      · rw [hLaws.sideForceLineIntegral]
        simp only [hGeometry.currentDirectedTangents,
          hGeometry.currentDirectedSidePaths, hField.fieldFormula]
        rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .top u)]
        simp [hL]
      · constructor
        · rw [hLaws.sideForceLineIntegral]
          simp only [hGeometry.currentDirectedTangents,
            hGeometry.currentDirectedSidePaths, hField.fieldFormula]
          rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .right u)]
          simp [hL]
        · rw [hLaws.sideForceLineIntegral]
          simp only [hGeometry.currentDirectedTangents,
            hGeometry.currentDirectedSidePaths, hField.fieldFormula]
          rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .bottom u)]
          simp
  · have hCrossYZ (a b : ℝ) :
        spatialCross (a • axisVector .y) (b • axisVector .z) =
          (a * b) • axisVector .x := by
      ext i
      fin_cases i <;>
        simp [spatialCross, axisVector, crossProduct] <;>
        ring
    have hCrossXZ (a b : ℝ) :
        spatialCross (a • axisVector .x) (b • axisVector .z) =
          (-(a * b)) • axisVector .y := by
      ext i
      fin_cases i <;>
        simp [spatialCross, axisVector, crossProduct] <;>
        ring
    have hFieldOnSide (side : LoopSide) (u : ℝ) :
        (magneticFluxDensityInTeslas setup.fieldScale *
                (spacePointOfMeters (squareSidePointInMeters
                  (lengthInMeters setup.sideLength) side u)).val (2 : Fin 3) /
              lengthInMeters setup.sideLength) • axisVector .y +
          (magneticFluxDensityInTeslas setup.fieldScale *
                (spacePointOfMeters (squareSidePointInMeters
                  (lengthInMeters setup.sideLength) side u)).val (1 : Fin 3) /
              lengthInMeters setup.sideLength) • axisVector .z =
          match side with
          | .left =>
              (magneticFluxDensityInTeslas setup.fieldScale * u) • axisVector .z
          | .top =>
              magneticFluxDensityInTeslas setup.fieldScale • axisVector .z
          | .right =>
              (magneticFluxDensityInTeslas setup.fieldScale * (1 - u)) •
                axisVector .z
          | .bottom => 0 := by
      cases side <;>
        ext i <;>
        fin_cases i <;>
        simp [squareSidePointInMeters, sideStartVertex, vertexVectorInMeters,
          sideDisplacementInMeters, spacePointOfMeters, axisVector] <;>
        field_simp [hL] <;>
        ring
    have hIntegrand (side : LoopSide) (u : ℝ) :
        spatialCross
            (sideDisplacementInMeters (lengthInMeters setup.sideLength) side)
            ((magneticFluxDensityInTeslas setup.fieldScale *
                    (spacePointOfMeters (squareSidePointInMeters
                      (lengthInMeters setup.sideLength) side u)).val (2 : Fin 3) /
                  lengthInMeters setup.sideLength) • axisVector .y +
              (magneticFluxDensityInTeslas setup.fieldScale *
                    (spacePointOfMeters (squareSidePointInMeters
                      (lengthInMeters setup.sideLength) side u)).val (1 : Fin 3) /
                  lengthInMeters setup.sideLength) • axisVector .z) =
          match side with
          | .left =>
              (magneticFluxDensityInTeslas setup.fieldScale * u *
                lengthInMeters setup.sideLength) • axisVector .x
          | .top =>
              (-(magneticFluxDensityInTeslas setup.fieldScale *
                lengthInMeters setup.sideLength)) • axisVector .y
          | .right =>
              (-(magneticFluxDensityInTeslas setup.fieldScale * (1 - u) *
                lengthInMeters setup.sideLength)) • axisVector .x
          | .bottom => 0 := by
      rw [hFieldOnSide side u]
      cases side
      · simp only [sideDisplacementInMeters]
        rw [hCrossYZ]
        congr 1
        ring
      · simp only [sideDisplacementInMeters]
        rw [hCrossXZ]
        congr 1
        ring
      · simp only [sideDisplacementInMeters]
        rw [hCrossYZ]
        congr 1
        ring
      · simp [sideDisplacementInMeters, spatialCross]
    constructor
    · rw [hLaws.sideForceLineIntegral]
      simp only [hGeometry.currentDirectedTangents,
        hGeometry.currentDirectedSidePaths, hField.fieldFormula]
      rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .left u)]
      rw [intervalIntegral.integral_smul_const]
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_const_mul]
      norm_num
      simp only [smul_smul]
      congr 1
      ring
    · constructor
      · rw [hLaws.sideForceLineIntegral]
        simp only [hGeometry.currentDirectedTangents,
          hGeometry.currentDirectedSidePaths, hField.fieldFormula]
        rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .top u)]
        simp only [intervalIntegral.integral_const]
        norm_num
        simp only [smul_smul]
        congr 1
        ring
      · constructor
        · rw [hLaws.sideForceLineIntegral]
          simp only [hGeometry.currentDirectedTangents,
            hGeometry.currentDirectedSidePaths, hField.fieldFormula]
          rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .right u)]
          rw [intervalIntegral.integral_smul_const]
          rw [intervalIntegral.integral_neg]
          rw [intervalIntegral.integral_mul_const]
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral.integral_sub intervalIntegrable_const
            intervalIntegral.intervalIntegrable_id]
          norm_num
          simp only [smul_smul]
          congr 1
          ring
        · rw [hLaws.sideForceLineIntegral]
          simp only [hGeometry.currentDirectedTangents,
            hGeometry.currentDirectedSidePaths, hField.fieldFormula]
          rw [intervalIntegral.integral_congr (fun u _ => hIntegrand .bottom u)]
          simp

/-- The four labels printed beside the multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force vector, in newtons, printed beside an answer label. -/
def displayedForceVectorInNewtons
    (setup : SquareCurrentLoopSetup) : AnswerChoice → SpatialVector
  | .A =>
      (-(currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.fieldScale *
          lengthInMeters setup.sideLength / 2)) • axisVector .y
  | .B =>
      (-(currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.fieldScale *
          lengthInMeters setup.sideLength)) • axisVector .y
  | .C =>
      (currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.fieldScale *
          lengthInMeters setup.sideLength) • axisVector .y
  | .D => 0

/-- Dataset answer label retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
Blueprint theorem `thm:physics:phyx_mini_0952:target`.

The net magnetic force is `-I B₀ L e_y`; its magnitude is `I B₀ L` newtons
and its direction is negative `y`. This is the vector displayed as choice B.
-/
theorem problem_phyx_mini_0952
    (setup : SquareCurrentLoopSetup)
    (hScenario : MatchesWrittenSquareLoopScenario setup)
    (hFigure : MatchesSuppliedSquareLoopFigure setup)
    (hGeometry : HasDepictedSquareLoopGeometry setup)
    (hPhysical : HasPhysicalLoopParameters setup)
    (hField : HasSpecifiedNonuniformMagneticField setup)
    (hLaws : SatisfiesMagneticWireForceLaw setup) :
    forceVectorInNewtons setup.netMagneticForce =
        (-(currentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas setup.fieldScale *
            lengthInMeters setup.sideLength)) • axisVector .y ∧
      ‖forceVectorInNewtons setup.netMagneticForce‖ =
        currentInAmperes setup.currentMagnitude *
          magneticFluxDensityInTeslas setup.fieldScale *
          lengthInMeters setup.sideLength ∧
      PointsInAxisDirection
        (forceVectorInNewtons setup.netMagneticForce) .negativeY := by
  rcases force_on_each_side setup hGeometry hField hLaws with
    ⟨hleft, htop, hright, hbottom⟩
  have hMagnitude :
      0 < currentInAmperes setup.currentMagnitude *
        magneticFluxDensityInTeslas setup.fieldScale *
        lengthInMeters setup.sideLength :=
    mul_pos
      (mul_pos hPhysical.currentMagnitudePositive hPhysical.fieldScalePositive)
      hPhysical.sideLengthPositive
  have hNet :
      forceVectorInNewtons setup.netMagneticForce =
        (-(currentInAmperes setup.currentMagnitude *
            magneticFluxDensityInTeslas setup.fieldScale *
            lengthInMeters setup.sideLength)) • axisVector .y := by
    rw [hLaws.netForceIsSumOfSideForces]
    classical
    rw [show (Finset.univ : Finset LoopSide) =
        {.left, .top, .right, .bottom} by decide]
    simp [hleft, htop, hright, hbottom]
  refine ⟨hNet, ?_, ?_⟩
  · rw [hNet, norm_smul]
    simp only [Real.norm_eq_abs]
    rw [abs_neg, abs_of_pos hMagnitude]
    simp [axisVector]
  · refine ⟨currentInAmperes setup.currentMagnitude *
        magneticFluxDensityInTeslas setup.fieldScale *
        lengthInMeters setup.sideLength, hMagnitude, ?_⟩
    rw [hNet]
    simp [axisDirectionVector, smul_neg, neg_smul]

end PhyXMiniProblems.ProblemPhyXMini0952
