import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0609

open Dimension

/-!
# Transverse magnetic field under a Lorentz boost

The laboratory frame `S` has zero electric field and a magnetic field along
the positive `z`-axis.  A second inertial frame `SPrime` moves with velocity
`v` relative to `S`.  The requested quantity is the component of the magnetic
field in `SPrime` perpendicular to `v`.

The rectangular current loop and all labels visible in image 609 are retained
as physical data even though they do not enter the Lorentz field-transformation
calculation.  In particular, the primary image resolves the generated
caption's reversed dimension labels: `L` is the `x`-extent and `H` is the
vertical `z`-extent.
-/

/-! ## Dimensionful loop quantities and spatial-vector operations -/

/-- A three-dimensional spatial vector in Physlib's Euclidean space. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Electric current has physical dimension charge per unit time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- A magnetic dipole moment has dimension current times area. -/
def magneticMomentDimension : Dimension :=
  electricCurrentDimension * L𝓭 * L𝓭

/-- Torque has the same physical dimension as energy. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev CurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A unit-independent magnetic-moment vector. -/
abbrev MagneticMomentQuantity : Type :=
  Dimensionful (WithDim magneticMomentDimension SpatialVector)

/-- A unit-independent torque vector. -/
abbrev TorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Coherent-SI scalar readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI vector readout of a dimensionful spatial vector. -/
def vectorSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity UnitChoices.SI).val

/-- The three coordinate axes appearing in the prose and the figure. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Unit coordinate vector associated with a labelled axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single 0 1
  | .y => EuclideanSpace.single 1 1
  | .z => EuclideanSpace.single 2 1

/-- A vector points strictly along the positive direction of a labelled axis. -/
def PointsAlongPositiveAxis
    (vector : SpatialVector) (axis : CoordinateAxis) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧ vector = magnitude • axisVector axis

/-- Mathlib's ordinary three-dimensional cross product, transported to `SpatialVector`. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-!
The component perpendicular to a unit direction `axis`.  Unit normalization
is an explicit admissibility premise below rather than being hidden in this
geometric definition.
-/
def perpendicularComponent
    (axis vector : SpatialVector) : SpatialVector :=
  vector - (inner ℝ vector axis) • axis

/-! ## Frames, loop geometry, and primary-image vocabulary -/

/-- The laboratory frame and the moving inertial frame. -/
inductive InertialFrame where
  | S
  | SPrime
  deriving DecidableEq, Fintype, Repr

/-- Coordinate planes relevant to the rectangular loop. -/
inductive CoordinatePlane where
  | xy
  | xz
  | yz
  deriving DecidableEq, Repr

/-- Sense in which the current circulates when viewed from a positive axis. -/
inductive CirculationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Literal dimension labels printed in the supplied image. -/
inductive DimensionLabel where
  | H
  | L
  deriving DecidableEq, Repr

/-- Vector and current labels printed beside arrows in the supplied image. -/
inductive FigureArrowLabel where
  | B
  | mu
  | I
  | tau
  deriving DecidableEq, Fintype, Repr

/-- Positive coordinate direction assigned to a straight vector arrow or axis. -/
inductive PositiveAxisDirection where
  | positiveX
  | positiveY
  | positiveZ
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence visible in image 609. -/
structure RectangularCurrentLoopFigure where
  coordinateAxisShown : CoordinateAxis → Bool
  loopPlaneShown : CoordinatePlane
  loopSurroundsOrigin : Bool
  extentLabelAlong : CoordinateAxis → Option DimensionLabel
  arrowLabelShown : FigureArrowLabel → Bool
  magneticFieldArrowDirection : PositiveAxisDirection
  magneticMomentArrowDirection : PositiveAxisDirection
  torqueAxisDirection : PositiveAxisDirection
  currentSenseViewedFromPositiveY : CirculationSense
  hasCalibratedMetricScale : Bool

/-! ## Independent physical setup -/

/-!
The loop quantities, frame-dependent electromagnetic fields, two coordinate
descriptions of one observation event, and relative-motion parameters are
independent data.  The magnetic field in `SPrime` is deliberately not defined
from `γ` or from an answer choice.
-/
structure MovingFrameMagneticFieldSetup where
  loopPlane : CoordinatePlane
  loopCenteredAtOrigin : Bool
  /-- The side labelled `H`, extending in the `z` direction in the image. -/
  loopExtentH : LengthQuantity
  /-- The side labelled `L`, extending in the `x` direction in the image. -/
  loopExtentL : LengthQuantity
  loopCurrent : CurrentQuantity
  currentSenseViewedFromPositiveY : CirculationSense
  magneticMoment : MagneticMomentQuantity
  torque : TorqueQuantity
  electricFieldMeasuredIn : InertialFrame → Electromagnetism.ElectricField
  magneticFieldMeasuredIn : InertialFrame → Electromagnetism.MagneticField
  eventTimeIn : InertialFrame → Time
  eventPositionIn : InertialFrame → Space 3
  magneticFieldMagnitudeBInS : ℝ
  /-- Dimensionless signed speed `β = |v|/c`, with sign encoding direction. -/
  speedFractionOfLight : ℝ
  /-- Unit vector specifying the direction of `SPrime`'s motion relative to `S`. -/
  boostDirection : SpatialVector
  /--
  Component readout of the relative velocity in the same coherent units used
  by `vacuumSpeedOfLight`.
  -/
  relativeVelocityReadout : SpatialVector
  vacuumSpeedOfLight : SpeedOfLight
  figure : RectangularCurrentLoopFigure

/-- Electric-field vector at the selected event in a specified frame. -/
def electricVectorAt
    (setup : MovingFrameMagneticFieldSetup)
    (frame : InertialFrame) : SpatialVector :=
  setup.electricFieldMeasuredIn frame
    (setup.eventTimeIn frame) (setup.eventPositionIn frame)

/-- Magnetic-field vector at the selected event in a specified frame. -/
def magneticVectorAt
    (setup : MovingFrameMagneticFieldSetup)
    (frame : InertialFrame) : SpatialVector :=
  setup.magneticFieldMeasuredIn frame
    (setup.eventTimeIn frame) (setup.eventPositionIn frame)

/-! ## Scenario, physical admissibility, and figure readouts -/

/-- Prose-level assignments, including `(E, B) = (0, B zHat)` in frame `S`. -/
structure MatchesMovingFrameMagneticFieldScenario
    (setup : MovingFrameMagneticFieldSetup) : Prop where
  loopLiesInXZPlane : setup.loopPlane = .xz
  loopSurroundsOrigin : setup.loopCenteredAtOrigin = true
  currentIsCounterclockwiseFromPositiveY :
    setup.currentSenseViewedFromPositiveY = .counterclockwise
  electricFieldVanishesInS : electricVectorAt setup .S = 0
  magneticFieldPointsAlongPositiveZ :
    magneticVectorAt setup .S =
      setup.magneticFieldMagnitudeBInS • axisVector .z
  magneticMomentPointsAlongPositiveY :
    PointsAlongPositiveAxis (vectorSIReadout setup.magneticMoment) .y
  torquePointsAlongPositiveX :
    PointsAlongPositiveAxis (vectorSIReadout setup.torque) .x

/-- Positivity, subluminality, and normalization conditions for the setup. -/
structure HasPhysicalMovingFrameParameters
    (setup : MovingFrameMagneticFieldSetup) : Prop where
  extentHPositive : 0 < nonnegativeSIReadout setup.loopExtentH
  extentLPositive : 0 < nonnegativeSIReadout setup.loopExtentL
  currentPositive : 0 < nonnegativeSIReadout setup.loopCurrent
  magneticFieldMagnitudePositive : 0 < setup.magneticFieldMagnitudeBInS
  boostIsSubluminal : |setup.speedFractionOfLight| < 1
  boostDirectionIsUnit : ‖setup.boostDirection‖ = 1
  velocityMatchesBetaAndDirection :
    setup.relativeVelocityReadout =
      (setup.speedFractionOfLight * setup.vacuumSpeedOfLight.val) •
        setup.boostDirection

/-!
Primary-image evidence.  The raster places `H` along the vertical `z` extent
and `L` along the slanted `x` extent, resolving the reversed assignment in the
auxiliary caption in favor of the image and scenario prose.
-/
structure MatchesSuppliedRectangularCurrentLoopFigure
    (setup : MovingFrameMagneticFieldSetup) : Prop where
  everyCoordinateAxisShown :
    ∀ axis, setup.figure.coordinateAxisShown axis = true
  loopShownInXZPlane : setup.figure.loopPlaneShown = .xz
  loopShownAroundOrigin : setup.figure.loopSurroundsOrigin = true
  heightLabelHAlongZ : setup.figure.extentLabelAlong .z = some .H
  lengthLabelLAlongX : setup.figure.extentLabelAlong .x = some .L
  noYExtentLabel : setup.figure.extentLabelAlong .y = none
  everyArrowLabelShown :
    ∀ label, setup.figure.arrowLabelShown label = true
  magneticFieldArrowPointsPositiveZ :
    setup.figure.magneticFieldArrowDirection = .positiveZ
  magneticMomentArrowPointsPositiveY :
    setup.figure.magneticMomentArrowDirection = .positiveY
  torqueIsDrawnAboutPositiveX :
    setup.figure.torqueAxisDirection = .positiveX
  currentArrowIsCounterclockwiseFromPositiveY :
    setup.figure.currentSenseViewedFromPositiveY = .counterclockwise
  drawingHasNoCalibratedMetricScale :
    setup.figure.hasCalibratedMetricScale = false

/-! ## Governing Lorentz field-transformation law -/

/-!
For the convention that `SPrime` moves with velocity `v` relative to `S`, the
general transverse magnetic-field law at corresponding events is

`B'_perp = γ(β) (B_perp - (1/c²) (v × E))`.

The electric mixing term is retained, so the desired zero-electric-field
specialization is not assumed here.
-/
structure SatisfiesLorentzElectromagneticFieldTransformation
    (setup : MovingFrameMagneticFieldSetup) : Prop where
  transverseMagneticTransformation :
    perpendicularComponent setup.boostDirection
        (magneticVectorAt setup .SPrime) =
      LorentzGroup.γ setup.speedFractionOfLight •
        (perpendicularComponent setup.boostDirection
            (magneticVectorAt setup .S) -
          (1 / setup.vacuumSpeedOfLight.val ^ 2) •
            spatialCross setup.relativeVelocityReadout
              (electricVectorAt setup .S))

/-! ## Answer choices and current target -/

/-- The four answer-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Subscript printed on the magnetic-field symbol in an answer choice. -/
inductive FieldSubscript where
  | gamma
  | alpha
  | beta
  | delta
  deriving DecidableEq, Fintype, Repr

/-- Literal mapping from the printed choices to their displayed subscripts. -/
def displayedSubscript : AnswerChoice → FieldSubscript
  | .A => .gamma
  | .B => .alpha
  | .C => .beta
  | .D => .delta

/-!
With zero electric field in `S`, the general Lorentz law reduces to the
requested result: the component of `B'` perpendicular to the relative velocity
is `γ(β)` times the corresponding component of `B` in `S`.  This is the
quantity denoted `B_gamma` by answer choice A.
-/
theorem perpendicularMagneticFieldInMovingFrame_eq_gamma_smul
    (setup : MovingFrameMagneticFieldSetup)
    (hScenario : MatchesMovingFrameMagneticFieldScenario setup)
    (hPhysical : HasPhysicalMovingFrameParameters setup)
    (hFigure : MatchesSuppliedRectangularCurrentLoopFigure setup)
    (hLorentz : SatisfiesLorentzElectromagneticFieldTransformation setup) :
    perpendicularComponent setup.boostDirection
        (magneticVectorAt setup .SPrime) =
      LorentzGroup.γ setup.speedFractionOfLight •
        perpendicularComponent setup.boostDirection
          (magneticVectorAt setup .S) := by
  rw [hLorentz.transverseMagneticTransformation,
    hScenario.electricFieldVanishesInS]
  simp [spatialCross]

end PhyXMiniProblems.ProblemPhyXMini0609
