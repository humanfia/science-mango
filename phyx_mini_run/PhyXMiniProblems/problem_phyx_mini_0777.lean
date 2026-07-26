import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Net torque on a square plate

A square metal plate of side `0.180 m` is pivoted about the perpendicular axis
through its center `O`.  In the primary image, positive `x` points right,
positive `y` points up, and positive signed torque is counterclockwise (out of
the page).  Forces `F₁` and `F₂` point downward at the upper-right and
upper-left corners respectively.  Force `F₃` points up and right along a
`45°` diagonal from the lower-right corner.

The image is treated as primary evidence: its `F₂` arrow points downward even
though the auxiliary caption says upward.  With the displayed values, the
exact torque is slightly above `2.50 N m`; answer B is its value rounded to the
hundredth shown by the choices.

Physical lengths, positions, forces, and torque use Physlib's unit-independent
`Dimensionful (WithDim ...)` representation.  Real numbers below are only
coherent-unit readouts, an angle measured in radians, or figure/display data.

Assumption/target boundary:

* `MatchesProblemStatement` contains the stated material, planar setup, side
  length, and force magnitudes.
* `MatchesPrimaryFigure` contains only labels, arrow placements/directions,
  and the two `0.180 m` and one `45°` readouts visible in the bitmap.
* `MatchesSquarePlateGeometry` and `MatchesDisplayedForceGeometry` express the
  corresponding Cartesian geometry.
* `SatisfiesPlanarTorqueLaw` is the governing relation
  `τ_z = ∑ (r_x F_y - r_y F_x)` in every coherent unit system.
* There are no previous-part results.
* The exact net torque and its agreement with answer B occur only in the
  theorem conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0777

open Dimension

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  L𝓭 * forceDimension

/-- Vectors in the plane of the plate. -/
abbrev PlanarVector : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- A unit-independent nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent position vector in the plane of the plate. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlanarVector)

/-- A unit-independent force vector in the plane of the plate. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- A signed torque component about the axis perpendicular to the plate. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Coordinate `0`, pointing right in the primary image. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, pointing upward in the primary image. -/
def yAxis : Fin 2 := 1

/-- Read a nonnegative physical scalar in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a planar physical vector in a coherent unit system. -/
def planarVectorReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d PlanarVector)) : PlanarVector :=
  (quantity units).val

/-- Read a signed physical scalar in a coherent unit system. -/
def signedScalarReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI length

/-- Cartesian metre readout of a position in the plate. -/
def positionInMeters (position : PlanarPositionQuantity) : PlanarVector :=
  planarVectorReadout UnitChoices.SI position

/-- Cartesian newton readout of a planar force. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  planarVectorReadout UnitChoices.SI force

/-- Euclidean magnitude, in newtons, of a planar physical force. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- Signed newton-metre readout, positive for counterclockwise torque. -/
def torqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  signedScalarReadout UnitChoices.SI torque

/--
The out-of-plane component of the moment of a force whose lever-arm and force
coordinates have been read in one coherent unit system.
-/
def planarMomentReadout (leverArm force : PlanarVector) : ℝ :=
  leverArm xAxis * force yAxis - leverArm yAxis * force xAxis

/-! ## Named objects and literal primary-figure content -/

/-- Distinguished center and corners of the square plate. -/
inductive PlatePoint where
  | pivotO
  | upperLeft
  | upperRight
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- The three force labels printed beside the red arrows. -/
inductive AppliedForceLabel where
  | F1
  | F2
  | F3
  deriving DecidableEq, Fintype, Repr

/-- The two separate side-length labels visible in the primary image. -/
inductive SideLengthLabel where
  | top
  | left
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of the force arrows in the image. -/
inductive ArrowDirection where
  | downward
  | upwardRight
  deriving DecidableEq, Repr

/-- Material category stated for the plate. -/
inductive PlateMaterial where
  | metal
  | other
  deriving DecidableEq, Repr

/-- The corner at which each force arrow is applied in image `777.png`. -/
def expectedApplicationPoint : AppliedForceLabel → PlatePoint
  | .F1 => .upperRight
  | .F2 => .upperLeft
  | .F3 => .lowerRight

/-- The arrow direction read directly from image `777.png`. -/
def expectedArrowDirection : AppliedForceLabel → ArrowDirection
  | .F1 => .downward
  | .F2 => .downward
  | .F3 => .upwardRight

/-- Literal labels and qualitative incidences transcribed from the bitmap. -/
structure SuppliedPlateFigure where
  showsSquarePlate : Bool
  showsPivotLabelO : Bool
  showsForceArrow : AppliedForceLabel → Bool
  forceApplicationPoint : AppliedForceLabel → PlatePoint
  forceArrowDirection : AppliedForceLabel → ArrowDirection
  showsSideLengthLabel : SideLengthLabel → Bool
  sideLengthLabelInMeters : SideLengthLabel → ℝ
  showsF3AngleArc : Bool
  f3AngleLabelInDegrees : ℝ

/-- Description of the pivot axis stated in the prose. -/
structure RotationAxisGeometry where
  pointOnAxis : PlatePoint
  perpendicularToPlate : Bool

/--
Independent physical quantities in the plate experiment.  In particular,
`netTorqueAboutO` is an unknown physical torque constrained only by the
governing law below; it is not defined from an answer value.
-/
structure SquarePlateTorqueSetup where
  material : PlateMaterial
  sideLength : LengthQuantity
  positionOf : PlatePoint → PlanarPositionQuantity
  appliedForce : AppliedForceLabel → PlanarForceQuantity
  applicationPoint : AppliedForceLabel → PlatePoint
  f3AngleFromPositiveXInRadians : ℝ
  netTorqueAboutO : SignedTorqueQuantity
  rotationAxis : RotationAxisGeometry
  plateAndForcesCoplanar : Bool
  figure : SuppliedPlateFigure

/-! ## Stated data, primary-image evidence, geometry, and governing law -/

/-- Numerical and categorical data stated in the problem prose. -/
structure MatchesProblemStatement (setup : SquarePlateTorqueSetup) : Prop where
  plateIsMetal : setup.material = .metal
  sideLengthMeters : lengthInMeters setup.sideLength = 9 / 50
  force1MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F1) = 18
  force2MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F2) = 26
  force3MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F3) = 14
  axisPassesThroughO : setup.rotationAxis.pointOnAxis = .pivotO
  axisIsPerpendicular : setup.rotationAxis.perpendicularToPlate = true
  allForcesLieInPlate : setup.plateAndForcesCoplanar = true

/--
Primary-image evidence, including the downward `F₂` arrow that conflicts with
the auxiliary prose caption.  No torque value or answer choice occurs here.
-/
structure MatchesPrimaryFigure (setup : SquarePlateTorqueSetup) : Prop where
  squareIsShown : setup.figure.showsSquarePlate = true
  pivotOIsShown : setup.figure.showsPivotLabelO = true
  everyForceArrowIsShown :
    ∀ label, setup.figure.showsForceArrow label = true
  displayedApplicationPoints :
    ∀ label,
      setup.figure.forceApplicationPoint label = expectedApplicationPoint label
  physicalApplicationPointsMatchFigure :
    ∀ label,
      setup.applicationPoint label = setup.figure.forceApplicationPoint label
  displayedArrowDirections :
    ∀ label,
      setup.figure.forceArrowDirection label = expectedArrowDirection label
  bothSideLabelsAreShown :
    ∀ label, setup.figure.showsSideLengthLabel label = true
  displayedSideLengths :
    ∀ label, setup.figure.sideLengthLabelInMeters label = 9 / 50
  sideLabelsMeasurePhysicalPlate :
    ∀ label,
      setup.figure.sideLengthLabelInMeters label =
        lengthInMeters setup.sideLength
  angleArcIsShown : setup.figure.showsF3AngleArc = true
  displayedAngleDegrees : setup.figure.f3AngleLabelInDegrees = 45
  angleLabelMeasuresF3Direction :
    setup.f3AngleFromPositiveXInRadians =
      setup.figure.f3AngleLabelInDegrees * Real.pi / 180

/-- Expected horizontal coordinate of each named point on a centered square. -/
def expectedXCoordinateInMeters (side : ℝ) : PlatePoint → ℝ
  | .pivotO => 0
  | .upperLeft => -side / 2
  | .upperRight => side / 2
  | .lowerLeft => -side / 2
  | .lowerRight => side / 2

/-- Expected vertical coordinate of each named point on a centered square. -/
def expectedYCoordinateInMeters (side : ℝ) : PlatePoint → ℝ
  | .pivotO => 0
  | .upperLeft => side / 2
  | .upperRight => side / 2
  | .lowerLeft => -side / 2
  | .lowerRight => -side / 2

/--
Cartesian realization of the square whose center `O` is the pivot.  This
contains only geometry derived from the side length, not a torque result.
-/
structure MatchesSquarePlateGeometry (setup : SquarePlateTorqueSetup) : Prop where
  horizontalCoordinates :
    ∀ point,
      positionInMeters (setup.positionOf point) xAxis =
        expectedXCoordinateInMeters (lengthInMeters setup.sideLength) point
  verticalCoordinates :
    ∀ point,
      positionInMeters (setup.positionOf point) yAxis =
        expectedYCoordinateInMeters (lengthInMeters setup.sideLength) point

/--
The force directions shown by the arrows, written in Cartesian components.
The angle is kept as an independent radian readout linked to the `45°` label
by `MatchesPrimaryFigure`.
-/
structure MatchesDisplayedForceGeometry
    (setup : SquarePlateTorqueSetup) : Prop where
  force1HorizontalComponent :
    forceVectorInNewtons (setup.appliedForce .F1) xAxis = 0
  force1PointsDownward :
    forceVectorInNewtons (setup.appliedForce .F1) yAxis =
      -forceMagnitudeInNewtons (setup.appliedForce .F1)
  force2HorizontalComponent :
    forceVectorInNewtons (setup.appliedForce .F2) xAxis = 0
  force2PointsDownward :
    forceVectorInNewtons (setup.appliedForce .F2) yAxis =
      -forceMagnitudeInNewtons (setup.appliedForce .F2)
  force3HorizontalComponent :
    forceVectorInNewtons (setup.appliedForce .F3) xAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F3) *
        Real.cos setup.f3AngleFromPositiveXInRadians
  force3VerticalComponent :
    forceVectorInNewtons (setup.appliedForce .F3) yAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F3) *
        Real.sin setup.f3AngleFromPositiveXInRadians

/--
The governing moment-of-force law in every coherent unit system.  It relates
the independent net-torque quantity to the sum of the three moments about
`O`, without supplying any numerical result.
-/
structure SatisfiesPlanarTorqueLaw (setup : SquarePlateTorqueSetup) : Prop where
  netTorqueIsSumOfForceMoments :
    ∀ units : UnitChoices,
      signedScalarReadout units setup.netTorqueAboutO =
        ∑ label : AppliedForceLabel,
          planarMomentReadout
            (planarVectorReadout units
                (setup.positionOf (setup.applicationPoint label)) -
              planarVectorReadout units (setup.positionOf .pivotO))
            (planarVectorReadout units (setup.appliedForce label))

/-! ## Displayed answers and current target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Torque value in newton-metres printed beside each answer label. -/
def displayedTorqueInNewtonMeters : AnswerChoice → ℝ
  | .A => 3 / 2
  | .B => 5 / 2
  | .C => 5
  | .D => 9 / 2

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
The exact torque agrees with a displayed value to the hundredth-place
precision used for `2.50 N m`.
-/
def RoundsToDisplayedTorque
    (setup : SquarePlateTorqueSetup) (choice : AnswerChoice) : Prop :=
  |torqueInNewtonMeters setup.netTorqueAboutO -
      displayedTorqueInNewtonMeters choice| < 1 / 200

/--
The signed net torque is
`18/25 + (63/50)√2 N m`, positive (counterclockwise), and rounds to
`2.50 N m`, the dataset's answer B.

Blueprint: `thm:physics:phyx_mini_0777:target`.
-/
theorem problem_phyx_mini_0777
    (setup : SquarePlateTorqueSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : MatchesSquarePlateGeometry setup)
    (_forceGeometry : MatchesDisplayedForceGeometry setup)
    (_torqueLaw : SatisfiesPlanarTorqueLaw setup) :
    torqueInNewtonMeters setup.netTorqueAboutO =
        18 / 25 + 63 / 50 * Real.sqrt 2 ∧
      0 < torqueInNewtonMeters setup.netTorqueAboutO ∧
      RoundsToDisplayedTorque setup recordedAnswerChoice := by
  have happ (label : AppliedForceLabel) :
      setup.applicationPoint label = expectedApplicationPoint label := by
    rw [_figure.physicalApplicationPointsMatchFigure label,
      _figure.displayedApplicationPoints label]
  have hangle :
      setup.f3AngleFromPositiveXInRadians = Real.pi / 4 := by
    rw [_figure.angleLabelMeasuresF3Direction,
      _figure.displayedAngleDegrees]
    ring
  have hposX (point : PlatePoint) :
      planarVectorReadout UnitChoices.SI (setup.positionOf point) xAxis =
        expectedXCoordinateInMeters
          (lengthInMeters setup.sideLength) point := by
    simpa [positionInMeters] using
      _geometry.horizontalCoordinates point
  have hposY (point : PlatePoint) :
      planarVectorReadout UnitChoices.SI (setup.positionOf point) yAxis =
        expectedYCoordinateInMeters
          (lengthInMeters setup.sideLength) point := by
    simpa [positionInMeters] using
      _geometry.verticalCoordinates point
  have hf1x :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F1) xAxis = 0 := by
    simpa [forceVectorInNewtons] using
      _forceGeometry.force1HorizontalComponent
  have hf1y :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F1) yAxis = -18 := by
    simpa [forceVectorInNewtons, _problem.force1MagnitudeNewtons] using
      _forceGeometry.force1PointsDownward
  have hf2x :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F2) xAxis = 0 := by
    simpa [forceVectorInNewtons] using
      _forceGeometry.force2HorizontalComponent
  have hf2y :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F2) yAxis = -26 := by
    simpa [forceVectorInNewtons, _problem.force2MagnitudeNewtons] using
      _forceGeometry.force2PointsDownward
  have hf3x :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F3) xAxis = 7 * Real.sqrt 2 := by
    calc
      _ = forceMagnitudeInNewtons (setup.appliedForce .F3) *
            Real.cos setup.f3AngleFromPositiveXInRadians := by
        simpa [forceVectorInNewtons] using
          _forceGeometry.force3HorizontalComponent
      _ = 7 * Real.sqrt 2 := by
        rw [_problem.force3MagnitudeNewtons, hangle,
          Real.cos_pi_div_four]
        ring
  have hf3y :
      planarVectorReadout UnitChoices.SI
          (setup.appliedForce .F3) yAxis = 7 * Real.sqrt 2 := by
    calc
      _ = forceMagnitudeInNewtons (setup.appliedForce .F3) *
            Real.sin setup.f3AngleFromPositiveXInRadians := by
        simpa [forceVectorInNewtons] using
          _forceGeometry.force3VerticalComponent
      _ = 7 * Real.sqrt 2 := by
        rw [_problem.force3MagnitudeNewtons, hangle,
          Real.sin_pi_div_four]
        ring
  have htorque :=
    _torqueLaw.netTorqueIsSumOfForceMoments UnitChoices.SI
  change torqueInNewtonMeters setup.netTorqueAboutO = _ at htorque
  have h_univ :
      (Finset.univ : Finset AppliedForceLabel) = {.F1, .F2, .F3} := by
    decide
  rw [h_univ] at htorque
  simp [happ, planarMomentReadout, hposX, hposY, hf1x, hf1y,
    hf2x, hf2y, hf3x, hf3y, _problem.sideLengthMeters,
    expectedApplicationPoint, expectedXCoordinateInMeters,
    expectedYCoordinateInMeters] at htorque
  ring_nf at htorque
  have hexact :
      torqueInNewtonMeters setup.netTorqueAboutO =
        18 / 25 + 63 / 50 * Real.sqrt 2 := by
    rw [htorque]
    ring
  have hsqrtTwoSq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtTwoNonneg : 0 ≤ Real.sqrt 2 :=
    Real.sqrt_nonneg 2
  have hsqrtTwoLower : (141 / 100 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hsqrtTwoUpper : Real.sqrt 2 < (283 / 200 : ℝ) := by
    nlinarith
  refine ⟨hexact, ?_, ?_⟩
  · rw [hexact]
    positivity
  · simp only [RoundsToDisplayedTorque, recordedAnswerChoice,
      displayedTorqueInNewtonMeters, hexact]
    rw [abs_lt]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0777
