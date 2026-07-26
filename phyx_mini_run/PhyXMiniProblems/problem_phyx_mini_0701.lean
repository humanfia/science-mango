import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0701

open Dimension

/-!
# Signed torque exerted with a tilted wrench

The nut is the pivot.  A `20 cm` wrench extends `30°` above the positive
horizontal direction, and Luis applies a `100 N` force vertically downward at
its end.  The primary figure additionally labels the signed angle from the
wrench radius to the force as `phi = -120°` and marks the perpendicular moment
arm `d` from the socket to the force's vertical line of action.

Length, force, and torque remain unit-independent Physlib quantities.  Real
numbers below occur only at coherent-SI readout boundaries, as dimensionless
angles and diagram coordinates, or as values printed beside answer choices.
The torque observable is an independent axial-vector field constrained by
Mathlib's three-dimensional cross product.  The wrench and pull lie in the
`xy`-plane, and the signed answer is the `z` component of that torque vector;
it is not defined from the requested answer.

Assumption/target split:

* governing laws: polar decompositions of the lever-arm and force vectors in
  the `xy`-plane, the signed-angle relation, perpendicular-distance geometry,
  and the axial-vector law `tau = r cross F`;
* previous-part results: none;
* problem and figure readouts: `20 cm`, `30°`, `100 N`, downward pull,
  `phi = -120°`, socket/nut pivot, vertical line of action, and moment arm `d`;
* current target conclusions: `d = sqrt 3 / 10 m`,
  `tau_z = -10 sqrt 3 N m`, and displayed choice B as the nearest integer
  newton-metre value.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Three-dimensional coordinate vectors; the wrench diagram occupies the `xy`-plane. -/
abbrev SpatialVector : Type := Fin 3 → ℝ

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent spatial displacement vector from the nut to the pull. -/
abbrev DisplacementVectorQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A unit-independent spatial physical force vector. -/
abbrev SpatialForceQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- A nonnegative perpendicular distance from a pivot to a force line. -/
abbrev MomentArmQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent physical torque axial vector. -/
abbrev TorqueVectorQuantity : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a spatial displacement vector in coherent SI metres. -/
def displacementVectorInMeters
    (displacement : DisplacementVectorQuantity) : SpatialVector :=
  (displacement UnitChoices.SI).val

/-- Read a nonnegative force magnitude in coherent SI newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a spatial physical force vector in coherent SI newtons. -/
def forceVectorInNewtons (force : SpatialForceQuantity) : SpatialVector :=
  (force UnitChoices.SI).val

/-- Read the perpendicular moment arm in coherent SI metres. -/
def momentArmInMeters (momentArm : MomentArmQuantity) : ℝ :=
  ((momentArm UnitChoices.SI).val : ℝ)

/-- Read a physical torque axial vector in coherent SI newton-metres. -/
def torqueVectorInNewtonMeters (torque : TorqueVectorQuantity) : SpatialVector :=
  (torque UnitChoices.SI).val

/-- Read the signed `z` component of torque, positive out of the diagram. -/
def torqueZInNewtonMeters (torque : TorqueVectorQuantity) : ℝ :=
  torqueVectorInNewtonMeters torque 2

/-! ## Spatial embedding of the planar geometry and sign convention -/

/-- Convert an angle measured in degrees to its dimensionless radian value. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-- Unit direction in the `xy`-plane at a counterclockwise angle from the positive `x`-axis. -/
def unitVectorAtAngleDegrees (degrees : ℝ) : SpatialVector :=
  ![Real.cos (degreesToRadians degrees),
    Real.sin (degreesToRadians degrees),
    0]

/-- The two senses of rotation about the nut. -/
inductive RotationSense where
  | counterclockwise
  | clockwise
  deriving DecidableEq, Repr

/-! ## Physical setup and primary-image vocabulary -/

/-- Physical objects and geometric constructions visible in image `701.png`. -/
inductive FigureObject where
  | nut
  | wrench
  | socketOpening
  | forceArrow
  | lineOfAction
  | momentArmSegment
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed in the supplied raster. -/
inductive FigureLabel where
  | length20Centimeters
  | handleAngle30Degrees
  | phiMinus120Degrees
  | force100Newtons
  | luisPull
  | lineOfAction
  | momentArmD
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions shown by the wrench and force arrows. -/
inductive FigureDirection where
  | upperRight
  | downward
  deriving DecidableEq, Repr

/-- Typed transcription of the incidence and annotation data in the figure. -/
structure WrenchTorqueFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  wrenchDirection : FigureDirection
  forceArrowDirection : FigureDirection
  forceArrowTailAtWrenchEnd : Bool
  forceLineOfActionIsVerticalDashed : Bool
  horizontalReferenceIsDashed : Bool
  momentArmRunsFromSocketToLineOfAction : Bool
  momentArmMarkedPerpendicularToLineOfAction : Bool
  phiArcRunsFromWrenchRadiusToForce : Bool

/-!
Independent quantities for the wrench experiment.  The scalar angles are
signed diagram readouts in degrees.  The physical lever arm, applied force,
perpendicular distance, and torque are separate observables related only by
the assumptions below.
-/
structure WrenchTorqueSetup where
  wrenchLength : LengthQuantity
  leverArmFromNutToPull : DisplacementVectorQuantity
  handleAngleDegrees : ℝ
  pullMagnitude : ForceMagnitudeQuantity
  pullForce : SpatialForceQuantity
  pullDirectionDegrees : ℝ
  signedAnglePhiDegrees : ℝ
  momentArmD : MomentArmQuantity
  torqueAboutNut : TorqueVectorQuantity
  positiveTorqueSense : RotationSense
  figure : WrenchTorqueFigure

/-! ## Problem data, primary-figure evidence, and governing laws -/

/-- Numerical and directional data stated in the problem and printed in the figure. -/
structure MatchesProblemData (setup : WrenchTorqueSetup) : Prop where
  wrenchLengthCentimeters :
    lengthInCentimeters setup.wrenchLength = 20
  handleTiltAboveHorizontalDegrees :
    setup.handleAngleDegrees = 30
  pullMagnitudeNewtons :
    forceMagnitudeInNewtons setup.pullMagnitude = 100
  pullIsStraightDownDegrees :
    setup.pullDirectionDegrees = -90
  signedAngleFromWrenchToPullDegrees :
    setup.signedAnglePhiDegrees = -120
  counterclockwiseTorqueIsPositive :
    setup.positiveTorqueSense = .counterclockwise

/-- Positivity conditions for a nondegenerate wrench and applied pull. -/
structure HasPhysicalWrenchParameters (setup : WrenchTorqueSetup) : Prop where
  wrenchLengthPositive : 0 < lengthInMeters setup.wrenchLength
  pullMagnitudePositive : 0 < forceMagnitudeInNewtons setup.pullMagnitude

/-!
Exact qualitative evidence transcribed from image `701.png`.  This records the
socket/nut pivot, the dashed references, the downward arrow, the line of
action, and the perpendicular segment labelled `d`, without assigning a
numerical moment arm or torque.
-/
structure MatchesSuppliedFigure (setup : WrenchTorqueSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  wrenchPointsUpperRight : setup.figure.wrenchDirection = .upperRight
  pullArrowPointsDown : setup.figure.forceArrowDirection = .downward
  pullAppliedAtWrenchEnd : setup.figure.forceArrowTailAtWrenchEnd = true
  verticalDashedLineOfAction :
    setup.figure.forceLineOfActionIsVerticalDashed = true
  dashedHorizontalAngleReference :
    setup.figure.horizontalReferenceIsDashed = true
  momentArmStartsAtSocket :
    setup.figure.momentArmRunsFromSocketToLineOfAction = true
  momentArmPerpendicularToLineOfAction :
    setup.figure.momentArmMarkedPerpendicularToLineOfAction = true
  signedPhiArcShown :
    setup.figure.phiArcRunsFromWrenchRadiusToForce = true

/-!
General spatial-vector geometry and torque laws in coherent SI coordinates.

The moment-arm field is constrained to be the perpendicular distance to the
force line.  The wrench and force directions are constrained to the `xy`-plane,
and the independent torque axial vector is constrained by Mathlib's general
three-dimensional `crossProduct`.  These laws quantify the model but do not
mention the numerical answer requested in this problem.
-/
structure SatisfiesWrenchTorqueLaws
    (setup : WrenchTorqueSetup) : Prop where
  leverArmHasWrenchLengthAndDirection :
    displacementVectorInMeters setup.leverArmFromNutToPull =
      lengthInMeters setup.wrenchLength •
        unitVectorAtAngleDegrees setup.handleAngleDegrees
  pullHasStatedMagnitudeAndDirection :
    forceVectorInNewtons setup.pullForce =
      forceMagnitudeInNewtons setup.pullMagnitude •
        unitVectorAtAngleDegrees setup.pullDirectionDegrees
  signedAngleIsDirectionDifference :
    setup.signedAnglePhiDegrees =
      setup.pullDirectionDegrees - setup.handleAngleDegrees
  momentArmIsPerpendicularDistance :
    momentArmInMeters setup.momentArmD =
      |(crossProduct
        (displacementVectorInMeters setup.leverArmFromNutToPull)
        (unitVectorAtAngleDegrees setup.pullDirectionDegrees)) 2|
  torqueIsLeverArmCrossForce :
    torqueVectorInNewtonMeters setup.torqueAboutNut =
      crossProduct
        (displacementVectorInMeters setup.leverArmFromNutToPull)
        (forceVectorInNewtons setup.pullForce)

/-! ## Displayed choices and target conclusions -/

/-- The four answer labels in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed torque, in newton-metres, printed beside each answer label. -/
def displayedTorqueInNewtonMeters : AnswerChoice → ℝ
  | .A => -15
  | .B => -17
  | .C => -19
  | .D => -21

/-- Dataset answer metadata, retained separately from the physical conclusion. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice is strictly closest to an exact signed torque. -/
def IsClosestDisplayedAnswer
    (choice : AnswerChoice) (exactTorqueInNewtonMeters : ℝ) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |exactTorqueInNewtonMeters - displayedTorqueInNewtonMeters choice| <
      |exactTorqueInNewtonMeters -
        displayedTorqueInNewtonMeters otherChoice|

/--
The perpendicular distance from the nut to the vertical force line is
`sqrt 3 / 10 m`, obtained from the `20 cm` radius at `30°`.
-/
lemma momentArmFromSuppliedGeometry
    (setup : WrenchTorqueSetup)
    (data : MatchesProblemData setup)
    (physical : HasPhysicalWrenchParameters setup)
    (figure : MatchesSuppliedFigure setup)
    (laws : SatisfiesWrenchTorqueLaws setup) :
    momentArmInMeters setup.momentArmD = Real.sqrt 3 / 10 := by
  rw [laws.momentArmIsPerpendicularDistance,
    laws.leverArmHasWrenchLengthAndDirection]
  have hlength : lengthInMeters setup.wrenchLength = (1 / 5 : ℝ) := by
    have h := data.wrenchLengthCentimeters
    simp only [lengthInCentimeters] at h
    linarith
  have h30 : degreesToRadians 30 = Real.pi / 6 := by
    rw [degreesToRadians]
    ring
  have hneg90 : degreesToRadians (-90) = -(Real.pi / 2) := by
    rw [degreesToRadians]
    ring
  rw [hlength, data.pullIsStraightDownDegrees,
    data.handleTiltAboveHorizontalDegrees]
  simp [unitVectorAtAngleDegrees, h30, hneg90, crossProduct,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg 3) (by norm_num))]
  ring

/-!
Luis's pull produces clockwise torque

`tau_z = (0.20 m)(100 N) sin(-120°) = -10 sqrt 3 N m`.

Consequently `-17 N m` (choice B) is the closest displayed integer value.
The source's recorded choice C is retained above only as dataset metadata; it
is inconsistent with the stated and pictured geometry.
-/
theorem problem_phyx_mini_0701
    (setup : WrenchTorqueSetup)
    (data : MatchesProblemData setup)
    (physical : HasPhysicalWrenchParameters setup)
    (figure : MatchesSuppliedFigure setup)
    (laws : SatisfiesWrenchTorqueLaws setup) :
    torqueZInNewtonMeters setup.torqueAboutNut =
        -10 * Real.sqrt 3 ∧
      IsClosestDisplayedAnswer .B
        (torqueZInNewtonMeters setup.torqueAboutNut) := by
  have hlength : lengthInMeters setup.wrenchLength = (1 / 5 : ℝ) := by
    have h := data.wrenchLengthCentimeters
    simp only [lengthInCentimeters] at h
    linarith
  have htorque :
      torqueZInNewtonMeters setup.torqueAboutNut =
        -10 * Real.sqrt 3 := by
    rw [torqueZInNewtonMeters, laws.torqueIsLeverArmCrossForce,
      laws.leverArmHasWrenchLengthAndDirection,
      laws.pullHasStatedMagnitudeAndDirection]
    rw [hlength, data.pullMagnitudeNewtons,
      data.pullIsStraightDownDegrees,
      data.handleTiltAboveHorizontalDegrees]
    have h30 : degreesToRadians 30 = Real.pi / 6 := by
      rw [degreesToRadians]
      ring
    have hneg90 : degreesToRadians (-90) = -(Real.pi / 2) := by
      rw [degreesToRadians]
      ring
    simp [unitVectorAtAngleDegrees, h30, hneg90, crossProduct,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    ring
  refine ⟨htorque, ?_⟩
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (17 / 10 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsqrt_upper : Real.sqrt 3 < (9 / 5 : ℝ) := by
    nlinarith
  intro other hother
  rw [htorque]
  fin_cases other
  · simp only [displayedTorqueInNewtonMeters]
    rw [abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)]
    linarith
  · contradiction
  · simp only [displayedTorqueInNewtonMeters]
    rw [abs_of_neg (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith
  · simp only [displayedTorqueInNewtonMeters]
    rw [abs_of_neg (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith

end PhyXMiniProblems.ProblemPhyXMini0701
