import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0677

open Dimension

/-!
# Magnitude of the sum of two planar forces

An object at the diagram origin is pulled by two forces. The first has
magnitude `6.00 N` and points `30.0°` above the positive horizontal axis; the
second has magnitude `5.00 N` and points along the positive vertical axis.
The supplied raster labels the two arrows `F₁` and `F₂` and marks the angle
`θ` between `F₁` and a dashed horizontal reference ray.

The force vectors below are unit-independent Physlib quantities with force
dimension `M L T⁻²`. Real numbers occur only at coherent-SI readout
boundaries, as dimensionless angles and diagram coordinates, and as the
numbers printed with the multiple-choice answers.
-/

/-! ## Physical force vectors and SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-independent planar physical force quantity. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- Dimensionless Cartesian coordinates used to locate the diagram origin. -/
abbrev DiagramCoordinate : Type := EuclideanSpace ℝ (Fin 2)

/-- Read a planar force vector in coherent SI units, i.e. newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- The Euclidean magnitude of an SI force-vector readout, in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- Convert an angle measured in degrees to its dimensionless radian value. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/--
The unit direction at a counterclockwise angle from the positive `x` axis.
Coordinate `0` is horizontal and coordinate `1` is vertical.
-/
def unitVectorAtAngleDegrees
    (degrees : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (degreesToRadians degrees),
      Real.sin (degreesToRadians degrees)]

/-! ## Named forces and primary-figure content -/

/-- The two force vectors named in the problem and raster. -/
inductive AppliedForceLabel where
  | forceOne
  | forceTwo
  deriving DecidableEq, Fintype, Repr

/-- Physical objects visibly represented in the supplied raster. -/
inductive FigureObject where
  | crate
  | upperHand
  | rightHand
  | forceOneRope
  | forceTwoRope
  deriving DecidableEq, Fintype, Repr

/-- Literal vector and angle labels printed in the supplied raster. -/
inductive FigureLabel where
  | forceVectorF1
  | forceVectorF2
  | theta
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of the two arrows in the primary image. -/
inductive FigureArrowDirection where
  | upward
  | upperRight
  deriving DecidableEq, Repr

/-- The direction visibly associated with each force arrow. -/
def expectedFigureArrowDirection :
    AppliedForceLabel → FigureArrowDirection
  | .forceOne => .upperRight
  | .forceTwo => .upward

/--
Typed qualitative content of image 677. The bitmap itself prints no force
magnitudes or numerical angle; those values come from the accompanying prose.
-/
structure ForceAdditionFigure where
  showsObject : FigureObject → Bool
  showsForceArrow : AppliedForceLabel → Bool
  showsLabel : FigureLabel → Bool
  arrowDirection : AppliedForceLabel → FigureArrowDirection
  arrowTailAtCrate : AppliedForceLabel → Bool
  ropeAttachedToCrate : AppliedForceLabel → Bool
  showsHorizontalDashedReferenceRay : Bool
  thetaArcBetweenForceOneAndHorizontal : Bool
  thetaLabelRefersTo : AppliedForceLabel
  containsNumericalForceMagnitude : Bool
  containsNumericalAngle : Bool

/--
Independent physical force vectors and their common application geometry.
The resultant is an observable field rather than a definition made from the
recorded answer. Diagram coordinates are dimensionless because only the
distinguished origin and coincidence of application points matter here.
-/
structure PlanarForceAdditionSetup where
  objectDiagramCoordinate : DiagramCoordinate
  forceApplicationCoordinate : AppliedForceLabel → DiagramCoordinate
  appliedForce : AppliedForceLabel → PlanarForceQuantity
  angleFromPositiveXAxisDegrees : AppliedForceLabel → ℝ
  resultantForce : PlanarForceQuantity
  figure : ForceAdditionFigure

/-! ## Scenario, data readouts, figure evidence, and governing laws -/

/-- Both forces act on the same object at the coordinate origin. -/
structure MatchesProblemScenario
    (setup : PlanarForceAdditionSetup) : Prop where
  objectIsAtOrigin : setup.objectDiagramCoordinate = 0
  eachForceActsAtObject :
    ∀ label,
      setup.forceApplicationCoordinate label =
        setup.objectDiagramCoordinate

/--
Numerical source data and directional readouts. Positive `y` is represented
by `90°` counterclockwise from positive `x`; no resultant value occurs here.
-/
structure MatchesProblemReadouts
    (setup : PlanarForceAdditionSetup) : Prop where
  forceOneMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .forceOne) = 6
  forceTwoMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .forceTwo) = 5
  forceOneAngleDegrees :
    setup.angleFromPositiveXAxisDegrees .forceOne = 30
  forceTwoPointsAlongPositiveY :
    setup.angleFromPositiveXAxisDegrees .forceTwo = 90

/--
Evidence transcribed from the primary image, including the two hands and
ropes, arrow directions, vector labels, dashed reference, and `θ` arc. The
last two fields record that the numerical data are not printed in the bitmap.
-/
structure MatchesSuppliedFigure
    (setup : PlanarForceAdditionSetup) : Prop where
  everyObjectShown :
    ∀ object, setup.figure.showsObject object = true
  bothForceArrowsShown :
    ∀ label, setup.figure.showsForceArrow label = true
  everyLiteralLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  displayedArrowDirections :
    ∀ label,
      setup.figure.arrowDirection label =
        expectedFigureArrowDirection label
  arrowTailsAtCrate :
    ∀ label, setup.figure.arrowTailAtCrate label = true
  ropesAttachedToCrate :
    ∀ label, setup.figure.ropeAttachedToCrate label = true
  horizontalReferenceRayShown :
    setup.figure.showsHorizontalDashedReferenceRay = true
  thetaArcShownInCorrectPlace :
    setup.figure.thetaArcBetweenForceOneAndHorizontal = true
  thetaLabelsForceOneAngle :
    setup.figure.thetaLabelRefersTo = .forceOne
  noNumericalMagnitudeInRaster :
    setup.figure.containsNumericalForceMagnitude = false
  noNumericalAngleInRaster :
    setup.figure.containsNumericalAngle = false

/--
Polar-coordinate interpretation of every applied-force readout. This is a
general direction convention and does not mention the requested resultant.
-/
structure ObeysPolarForceDirectionConvention
    (setup : PlanarForceAdditionSetup) : Prop where
  appliedForceFromMagnitudeAndAngle :
    ∀ label,
      forceVectorInNewtons (setup.appliedForce label) =
        forceMagnitudeInNewtons (setup.appliedForce label) •
          unitVectorAtAngleDegrees
            (setup.angleFromPositiveXAxisDegrees label)

/--
Vector superposition for simultaneous forces. It relates the independent
resultant observable to the two applied vectors, but does not state the
requested magnitude or any answer choice.
-/
structure ObeysForceSuperposition
    (setup : PlanarForceAdditionSetup) : Prop where
  resultantIsVectorSum :
    forceVectorInNewtons setup.resultantForce =
      forceVectorInNewtons (setup.appliedForce .forceOne) +
        forceVectorInNewtons (setup.appliedForce .forceTwo)

/-! ## Displayed answers and target conclusion -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The force magnitude, in newtons, displayed beside each answer label. -/
def displayedAnswerMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 6
  | .B => 8
  | .C => 19 / 2
  | .D => 5 / 2

/--
An exact magnitude agrees with a one-decimal displayed answer when their
absolute difference is less than half of one tenth of a newton.
-/
def MatchesDisplayedAnswerToNearestTenth
    (choice : AnswerChoice) (exactMagnitudeNewtons : ℝ) : Prop :=
  |exactMagnitudeNewtons - displayedAnswerMagnitudeInNewtons choice| < 1 / 20

/--
The exact vector sum has magnitude `√91 N`, which is represented by the
recorded one-decimal answer `C: 9.5 N`.

This conclusion is not a field of any setup or law structure: it must be
derived from the two source magnitudes, their directions, and vector
superposition.
-/
theorem resultantForceMagnitudeAndRecordedChoice
    (setup : PlanarForceAdditionSetup)
    (scenario : MatchesProblemScenario setup)
    (readouts : MatchesProblemReadouts setup)
    (figure : MatchesSuppliedFigure setup)
    (directions : ObeysPolarForceDirectionConvention setup)
    (superposition : ObeysForceSuperposition setup) :
    forceMagnitudeInNewtons setup.resultantForce = Real.sqrt 91 ∧
      MatchesDisplayedAnswerToNearestTenth .C
        (forceMagnitudeInNewtons setup.resultantForce) := by
  have hThirtyDegrees : degreesToRadians 30 = Real.pi / 6 := by
    rw [degreesToRadians]
    ring
  have hNinetyDegrees : degreesToRadians 90 = Real.pi / 2 := by
    rw [degreesToRadians]
    ring
  have hForceOne :
      forceVectorInNewtons (setup.appliedForce .forceOne) =
        !₂[3 * Real.sqrt 3, 3] := by
    rw [directions.appliedForceFromMagnitudeAndAngle,
      readouts.forceOneMagnitudeNewtons, readouts.forceOneAngleDegrees]
    ext i
    fin_cases i <;>
      simp [unitVectorAtAngleDegrees, hThirtyDegrees,
        Real.cos_pi_div_six, Real.sin_pi_div_six] <;>
      ring
  have hForceTwo :
      forceVectorInNewtons (setup.appliedForce .forceTwo) =
        !₂[0, 5] := by
    rw [directions.appliedForceFromMagnitudeAndAngle,
      readouts.forceTwoMagnitudeNewtons,
      readouts.forceTwoPointsAlongPositiveY]
    ext i
    fin_cases i <;>
      simp [unitVectorAtAngleDegrees, hNinetyDegrees]
  have hResultant :
      forceVectorInNewtons setup.resultantForce =
        !₂[3 * Real.sqrt 3, 8] := by
    rw [superposition.resultantIsVectorSum, hForceOne, hForceTwo]
    ext i
    fin_cases i <;> simp <;> norm_num
  have hMagnitude :
      forceMagnitudeInNewtons setup.resultantForce = Real.sqrt 91 := by
    rw [forceMagnitudeInNewtons, hResultant, EuclideanSpace.norm_eq]
    congr 1
    norm_num [Fin.sum_univ_succ]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  constructor
  · exact hMagnitude
  · rw [hMagnitude]
    unfold MatchesDisplayedAnswerToNearestTenth
    norm_num [displayedAnswerMagnitudeInNewtons]
    have hSqrt91Lower : (19 / 2 : ℝ) < Real.sqrt 91 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hSqrt91Upper : Real.sqrt 91 < (191 / 20 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    rw [abs_lt]
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0677
