import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Area

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0947

open Dimension

/-!
# Holding torque on a tilted rectangular current loop

A single rectangular loop is pivoted about its left, vertical side, which lies
on the `y`-axis.  The primary figure shows current flowing upward on that side,
across the top toward the free side, downward on the free side, and back along
the bottom.  The bottom edge is rotated by `30°` from positive `x` toward
negative `z`.  Consequently the current-oriented area normal has negative
`x` and negative `z` components.  In a uniform magnetic field along positive
`x`, the magnetic torque points along negative `y`; the external holding
torque therefore points along positive `y`.

All basic physical quantities are unit-independent `Dimensionful` values.
Real scalars and Euclidean vectors occur only as coherent-SI readouts,
dimensionless angles, or literal figure and answer-choice data.

Assumption/target split:

* `MatchesProblemStatement` records the stated current, field magnitude,
  pivot axis, rectangular one-turn topology, and uniform-field description;
* `MatchesPrimaryFigure` records the two side labels, the `30°` arc, the
  coordinate axes, and the four current arrows visible in image `947.png`;
* `MatchesRectangularLoopGeometry` relates those data to the area and the
  current-oriented unit normal;
* `ModelsUniformMagneticField`, `SatisfiesCurrentLoopMagneticMomentLaw`,
  `SatisfiesMagneticTorqueLaw`, and `SatisfiesStaticHoldingCondition` state
  the governing physical laws;
* there are no previous-part results; and
* the exact holding-torque vector and magnitude, its positive-`y` direction,
  and agreement with answer B occur only in `problem_phyx_mini_0947`.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Three-dimensional Euclidean vectors used for coherent-unit readouts. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A current-loop magnetic moment has dimension current times area. -/
def magneticMomentDimension : Dimension :=
  electricCurrentDimension * L𝓭 * L𝓭

/-- Torque has the energy dimension `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A unit-independent magnetic-flux-density vector. -/
abbrev MagneticFluxDensityVector : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension SpatialVector)

/-- A unit-independent magnetic-dipole-moment vector. -/
abbrev MagneticMomentVector : Type :=
  Dimensionful (WithDim magneticMomentDimension SpatialVector)

/-- A unit-independent torque vector. -/
abbrev TorqueVector : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Read a nonnegative dimensionful scalar in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a dimensionful spatial vector in coherent SI units. -/
def vectorSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity UnitChoices.SI).val

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read an area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  nonnegativeSIReadout area

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read a magnetic-flux-density vector in tesla coordinates. -/
def magneticFluxDensityVectorInTeslas
    (field : MagneticFluxDensityVector) : SpatialVector :=
  vectorSIReadout field

/-- Read a magnetic moment in ampere-square-metre coordinates. -/
def magneticMomentInAmpereSquareMeters
    (moment : MagneticMomentVector) : SpatialVector :=
  vectorSIReadout moment

/-- Read a torque in newton-metre coordinates. -/
def torqueInNewtonMeters (torque : TorqueVector) : SpatialVector :=
  vectorSIReadout torque

/-- Euclidean magnitude of a torque readout, in newton-metres. -/
def torqueMagnitudeInNewtonMeters (torque : TorqueVector) : ℝ :=
  ‖torqueInNewtonMeters torque‖

/-- Mathlib's ordinary cross product transported to `EuclideanSpace ℝ (Fin 3)`. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Dimensionless positive-`x` coordinate unit vector. -/
def xHat : SpatialVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Dimensionless positive-`y` coordinate unit vector. -/
def yHat : SpatialVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- Dimensionless positive-`z` coordinate unit vector. -/
def zHat : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) 1

/-- Convert a dimensionless degree readout to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Apparatus and literal primary-figure vocabulary -/

/-- The one closed-loop topology stated by the problem. -/
inductive LoopTopology where
  | singleTurnRectangle
  deriving DecidableEq, Repr

/-- Coordinate axes printed beside the loop. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- The four labelled geometric sides of the rectangular loop. -/
inductive LoopEdge where
  | pivotSide
  | top
  | freeSide
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- Traversal direction of a current arrow on a particular displayed edge. -/
inductive CurrentArrowTraversal where
  | upwardAlongPivot
  | pivotToFreeAcrossTop
  | downwardAlongFreeSide
  | freeToPivotAcrossBottom
  deriving DecidableEq, Repr

/-- Literal content transcribed from the supplied `239 × 297` raster. -/
structure RectangularLoopFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  coordinateAxisShown : CoordinateAxis → Bool
  loopEdgeShown : LoopEdge → Bool
  pivotSideCoincidesWithYAxis : Bool
  displayedHeightCentimeters : ℝ
  displayedWidthCentimeters : ℝ
  displayedBottomAngleDegrees : ℝ
  angleArcShown : Bool
  displayedCurrentAmperes : ℝ
  currentArrowTraversal : LoopEdge → CurrentArrowTraversal

/-!
Independent physical data for the loop and field.  The magnetic moment,
magnetic torque, and holding torque are independent observables constrained by
governing-law structures below; none is defined from an answer choice.
-/
structure RectangularCurrentLoopSetup where
  topology : LoopTopology
  pivotAxis : CoordinateAxis
  loopHeight : LengthMagnitude
  loopWidth : LengthMagnitude
  loopArea : DimArea
  currentMagnitude : ElectricCurrentMagnitude
  widthAngleFromPositiveXToNegativeZRadians : ℝ
  pivotAxisUnit : SpatialVector
  freeSideDisplacementUnit : SpatialVector
  currentOrientedAreaNormalUnit : SpatialVector
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  magneticFluxDensityVector : MagneticFluxDensityVector
  magneticField : Electromagnetism.MagneticField 3
  magneticMoment : MagneticMomentVector
  magneticTorque : TorqueVector
  holdingTorque : TorqueVector
  figure : RectangularLoopFigure

/-! ## Source data, geometry, and governing laws -/

/-- Numerical and qualitative data explicitly supplied in the problem prose. -/
structure MatchesProblemStatement
    (setup : RectangularCurrentLoopSetup) : Prop where
  loopIsSingleTurnRectangle : setup.topology = .singleTurnRectangle
  loopIsPivotedAboutYAxis : setup.pivotAxis = .y
  currentMagnitudeIsFifteenAmperes :
    currentInAmperes setup.currentMagnitude = 15
  fieldMagnitudeIsPointFourEightTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 12 / 25

/-!
Primary-image evidence and its calibration to physical quantities.  These
fields contain no torque value or answer-choice conclusion.
-/
structure MatchesPrimaryFigure
    (setup : RectangularCurrentLoopSetup) : Prop where
  rasterWidth : setup.figure.rasterWidthPixels = 239
  rasterHeight : setup.figure.rasterHeightPixels = 297
  everyCoordinateAxisIsShown :
    ∀ axis, setup.figure.coordinateAxisShown axis = true
  everyLoopEdgeIsShown :
    ∀ edge, setup.figure.loopEdgeShown edge = true
  pivotSideIsDrawnOnYAxis :
    setup.figure.pivotSideCoincidesWithYAxis = true
  displayedHeightIsEightCentimeters :
    setup.figure.displayedHeightCentimeters = 8
  heightLabelMeasuresPhysicalHeight :
    setup.figure.displayedHeightCentimeters =
      100 * lengthInMeters setup.loopHeight
  displayedWidthIsSixCentimeters :
    setup.figure.displayedWidthCentimeters = 6
  widthLabelMeasuresPhysicalWidth :
    setup.figure.displayedWidthCentimeters =
      100 * lengthInMeters setup.loopWidth
  bottomAngleArcIsShown : setup.figure.angleArcShown = true
  displayedBottomAngleIsThirtyDegrees :
    setup.figure.displayedBottomAngleDegrees = 30
  angleLabelMeasuresPhysicalAngle :
    setup.widthAngleFromPositiveXToNegativeZRadians =
      degreesToRadians setup.figure.displayedBottomAngleDegrees
  displayedCurrentIsFifteenAmperes :
    setup.figure.displayedCurrentAmperes = 15
  currentLabelMeasuresPhysicalCurrent :
    setup.figure.displayedCurrentAmperes =
      currentInAmperes setup.currentMagnitude
  pivotCurrentPointsUpward :
    setup.figure.currentArrowTraversal .pivotSide = .upwardAlongPivot
  topCurrentRunsTowardFreeSide :
    setup.figure.currentArrowTraversal .top = .pivotToFreeAcrossTop
  freeSideCurrentPointsDownward :
    setup.figure.currentArrowTraversal .freeSide = .downwardAlongFreeSide
  bottomCurrentReturnsToPivot :
    setup.figure.currentArrowTraversal .bottom = .freeToPivotAcrossBottom

/-!
Cartesian realization of the pictured rectangular geometry.  The free-side
displacement lies in the `x`-`z` plane, rotated from positive `x` toward
negative `z`.  Since current rises along the pivot side, the right-hand-rule
area normal is `yHat × freeSideDisplacementUnit`.  This is geometry and current
orientation only; it does not mention either torque.
-/
structure MatchesRectangularLoopGeometry
    (setup : RectangularCurrentLoopSetup) : Prop where
  pivotAxisPointsAlongPositiveY : setup.pivotAxisUnit = yHat
  freeSideDirectionFromMarkedAngle :
    setup.freeSideDisplacementUnit =
      Real.cos setup.widthAngleFromPositiveXToNegativeZRadians • xHat -
        Real.sin setup.widthAngleFromPositiveXToNegativeZRadians • zHat
  pivotAxisIsUnit : ‖setup.pivotAxisUnit‖ = 1
  freeSideDirectionIsUnit : ‖setup.freeSideDisplacementUnit‖ = 1
  currentOrientedAreaNormal :
    setup.currentOrientedAreaNormalUnit =
      spatialCross setup.pivotAxisUnit setup.freeSideDisplacementUnit
  currentOrientedAreaNormalIsUnit :
    ‖setup.currentOrientedAreaNormalUnit‖ = 1
  rectangleAreaLaw :
    areaInSquareMeters setup.loopArea =
      lengthInMeters setup.loopHeight * lengthInMeters setup.loopWidth

/-!
The field is spatially and temporally uniform and points along positive `x`.
Physlib's spacetime-dependent magnetic field is calibrated by the independent
dimensionful flux-density vector.
-/
structure ModelsUniformMagneticField
    (setup : RectangularCurrentLoopSetup) : Prop where
  fluxDensityVectorPointsPositiveX :
    magneticFluxDensityVectorInTeslas setup.magneticFluxDensityVector =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude • xHat
  physlibFieldIsUniform :
    ∀ time position,
      setup.magneticField time position =
        magneticFluxDensityVectorInTeslas setup.magneticFluxDensityVector

/-!
The magnetic moment of a one-turn planar current loop is current times area in
the current-oriented normal direction.  This governing law contains no torque
answer.
-/
structure SatisfiesCurrentLoopMagneticMomentLaw
    (setup : RectangularCurrentLoopSetup) : Prop where
  magneticMomentIsCurrentTimesArea :
    magneticMomentInAmpereSquareMeters setup.magneticMoment =
      (currentInAmperes setup.currentMagnitude *
          areaInSquareMeters setup.loopArea) •
        setup.currentOrientedAreaNormalUnit

/-! The magnetic torque on a dipole is `μ × B`. -/
structure SatisfiesMagneticTorqueLaw
    (setup : RectangularCurrentLoopSetup) : Prop where
  magneticTorqueIsMomentCrossField :
    torqueInNewtonMeters setup.magneticTorque =
      spatialCross
        (magneticMomentInAmpereSquareMeters setup.magneticMoment)
        (magneticFluxDensityVectorInTeslas setup.magneticFluxDensityVector)

/-!
To hold the loop fixed, the applied holding torque balances the magnetic
torque.  This is the static-equilibrium law, not the requested evaluated
holding torque.
-/
structure SatisfiesStaticHoldingCondition
    (setup : RectangularCurrentLoopSetup) : Prop where
  netTorqueVanishes :
    torqueInNewtonMeters setup.holdingTorque +
        torqueInNewtonMeters setup.magneticTorque = 0

/-! ## Direction and displayed answer choices -/

/-- A vector points strictly along the positive direction of an axis. -/
def PointsAlongPositiveAxis
    (vector : SpatialVector) (axis : CoordinateAxis) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    vector = magnitude •
      match axis with
      | .x => xHat
      | .y => yHat
      | .z => zHat

/-- Labels of the four displayed torque-magnitude choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Torque magnitude printed beside each choice, in newton-metres. -/
def displayedTorqueMagnitudeInNewtonMeters : AnswerChoice → ℝ
  | .A => 21 / 500
  | .B => 3 / 100
  | .C => 13 / 500
  | .D => 17 / 500

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Agreement after rounding a torque magnitude to the nearest `0.001 N m`. -/
def AgreesAtMillinewtonMeterPrecision
    (setup : RectangularCurrentLoopSetup) (choice : AnswerChoice) : Prop :=
  |torqueMagnitudeInNewtonMeters setup.holdingTorque -
      displayedTorqueMagnitudeInNewtonMeters choice| < 1 / 2000

/-!
The required holding torque is opposite the magnetic torque.  Its exact
magnitude is

`15 * (0.08 * 0.06) * 0.48 * cos (30°)
  = (108 / 3125) * cos (π / 6) N m`,

and it points along positive `y`.  This rounds to `0.030 N m`, answer B.

Blueprint: `thm:physics:phyx_mini_0947:target`.
-/
theorem problem_phyx_mini_0947
    (setup : RectangularCurrentLoopSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : MatchesRectangularLoopGeometry setup)
    (_uniformField : ModelsUniformMagneticField setup)
    (_momentLaw : SatisfiesCurrentLoopMagneticMomentLaw setup)
    (_magneticTorqueLaw : SatisfiesMagneticTorqueLaw setup)
    (_staticHolding : SatisfiesStaticHoldingCondition setup) :
    torqueInNewtonMeters setup.holdingTorque =
        ((108 / 3125) * Real.cos (Real.pi / 6)) • yHat ∧
      torqueMagnitudeInNewtonMeters setup.holdingTorque =
        (108 / 3125) * Real.cos (Real.pi / 6) ∧
      PointsAlongPositiveAxis
        (torqueInNewtonMeters setup.holdingTorque) .y ∧
      AgreesAtMillinewtonMeterPrecision setup recordedAnswerChoice := by
  have hheight : lengthInMeters setup.loopHeight = (2 : ℝ) / 25 := by
    linarith [_figure.displayedHeightIsEightCentimeters,
      _figure.heightLabelMeasuresPhysicalHeight]
  have hwidth : lengthInMeters setup.loopWidth = (3 : ℝ) / 50 := by
    linarith [_figure.displayedWidthIsSixCentimeters,
      _figure.widthLabelMeasuresPhysicalWidth]
  have harea : areaInSquareMeters setup.loopArea = (3 : ℝ) / 625 := by
    rw [_geometry.rectangleAreaLaw, hheight, hwidth]
    norm_num
  have hangle :
      setup.widthAngleFromPositiveXToNegativeZRadians = Real.pi / 6 := by
    rw [_figure.angleLabelMeasuresPhysicalAngle,
      _figure.displayedBottomAngleIsThirtyDegrees]
    unfold degreesToRadians
    ring
  have hnormal :
      setup.currentOrientedAreaNormalUnit =
        (-Real.sin (Real.pi / 6)) • xHat -
          Real.cos (Real.pi / 6) • zHat := by
    rw [_geometry.currentOrientedAreaNormal,
      _geometry.pivotAxisPointsAlongPositiveY,
      _geometry.freeSideDirectionFromMarkedAngle, hangle]
    ext i
    fin_cases i <;>
      simp [spatialCross, xHat, yHat, zHat, crossProduct]
  have hmoment :
      magneticMomentInAmpereSquareMeters setup.magneticMoment =
        ((9 : ℝ) / 125) •
          ((-Real.sin (Real.pi / 6)) • xHat -
            Real.cos (Real.pi / 6) • zHat) := by
    rw [_momentLaw.magneticMomentIsCurrentTimesArea,
      _problem.currentMagnitudeIsFifteenAmperes, harea, hnormal]
    norm_num
  have hfield :
      magneticFluxDensityVectorInTeslas setup.magneticFluxDensityVector =
        ((12 : ℝ) / 25) • xHat := by
    rw [_uniformField.fluxDensityVectorPointsPositiveX,
      _problem.fieldMagnitudeIsPointFourEightTeslas]
  have hmagnetic :
      torqueInNewtonMeters setup.magneticTorque =
        (-((108 : ℝ) / 3125 * Real.cos (Real.pi / 6))) • yHat := by
    rw [_magneticTorqueLaw.magneticTorqueIsMomentCrossField,
      hmoment, hfield]
    ext i
    fin_cases i <;>
      simp [spatialCross, xHat, yHat, zHat, crossProduct]
    all_goals ring
  have hholding :
      torqueInNewtonMeters setup.holdingTorque =
        ((108 : ℝ) / 3125 * Real.cos (Real.pi / 6)) • yHat := by
    have hneg :=
      eq_neg_of_add_eq_zero_left _staticHolding.netTorqueVanishes
    rw [hmagnetic] at hneg
    simpa using hneg
  have hcoeff_pos :
      0 < (108 : ℝ) / 3125 * Real.cos (Real.pi / 6) := by
    rw [Real.cos_pi_div_six]
    positivity
  have hmagnitude :
      torqueMagnitudeInNewtonMeters setup.holdingTorque =
        (108 : ℝ) / 3125 * Real.cos (Real.pi / 6) := by
    rw [torqueMagnitudeInNewtonMeters, hholding, norm_smul,
      Real.norm_eq_abs, abs_of_pos hcoeff_pos]
    simp [yHat]
  have hdirection :
      PointsAlongPositiveAxis
        (torqueInNewtonMeters setup.holdingTorque) .y := by
    refine
      ⟨(108 : ℝ) / 3125 * Real.cos (Real.pi / 6), hcoeff_pos, ?_⟩
    simpa using hholding
  have hagreement :
      AgreesAtMillinewtonMeterPrecision setup recordedAnswerChoice := by
    unfold AgreesAtMillinewtonMeterPrecision recordedAnswerChoice
    rw [hmagnitude]
    change
      |(108 / 3125 : ℝ) * Real.cos (Real.pi / 6) - 3 / 100| <
        1 / 2000
    rw [Real.cos_pi_div_six, abs_lt]
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      norm_num
    have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    constructor <;> nlinarith
  exact ⟨hholding, hmagnitude, hdirection, hagreement⟩

end PhyXMiniProblems.ProblemPhyXMini0947
