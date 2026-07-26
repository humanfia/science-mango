import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0760

open Dimension

/-!
# Direction of the water force on a horse-drawn barge

A horse pulls a barge through a canal with a `7900 N` tow force directed
`18 degrees` above the barge's positive `x` direction.  The barge has mass
`9500 kg` and accelerates at `0.12 m/s^2` along that positive direction.  The
question asks for the direction, relative to positive `x`, of the horizontal
force exerted by the water.

The primary bitmap shows the barge in water, the tow rope rising to the right,
a horizontal reference ray, the angle arc labelled `theta`, and the horse at
the rope's right endpoint.  It does not show an anchor, contrary to the
auxiliary generated caption.

Mass, planar acceleration, and planar force use Physlib's unit-independent
`Dimensionful (WithDim ...)` quantities.  Real vectors appear only as coherent
unit readouts, and directions use Mathlib's `Real.Angle`, so directions are
intrinsically taken modulo one full turn.

Assumption/target split:

* governing laws: straight-line acceleration, polar decomposition of each
  nonzero force vector, and Newton's second law for the two horizontal forces;
* previous-part results: none;
* data and figure readouts: `7900 N`, `18 degrees`, `9500 kg`, `0.12 m/s^2`,
  positive-`x` motion, and the rope/reference geometry visible in the bitmap;
* current target: the water-force direction is uniquely closest to the
  displayed `201 degrees`, namely answer C.
-/

/-! ## Dimensionful planar quantities and coherent readouts -/

/-- Two-dimensional Euclidean vectors in the horizontal canal plane. -/
abbrev PlanarVector : Type := EuclideanSpace ℝ (Fin 2)

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed planar physical acceleration vector. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension PlanarVector)

/-- A signed planar physical force vector. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- Coordinate `0`, the positive direction of barge motion. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, the side of the canal on which the horse is shown. -/
def yAxis : Fin 2 := 1

/-- The dimensionless unit vector along positive `x`. -/
def xHat : PlanarVector :=
  EuclideanSpace.single xAxis 1

/-- The dimensionless unit vector along positive `y`. -/
def yHat : PlanarVector :=
  EuclideanSpace.single yAxis 1

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

/-- Kilogram readout of the barge's physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI mass

/-- Cartesian SI readout of acceleration, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : PlanarVector :=
  planarVectorReadout UnitChoices.SI acceleration

/-- Cartesian SI readout of force, in newtons. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  planarVectorReadout UnitChoices.SI force

/-- Magnitude of a planar acceleration readout, in metres per second squared. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : ℝ :=
  ‖accelerationInMetersPerSecondSquared acceleration‖

/-- Magnitude of a planar force readout, in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- Convert a degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-- Interpret a degree readout as an angle modulo a full turn. -/
def angleFromDegrees (degrees : ℝ) : Real.Angle :=
  ((degreesToRadians degrees : ℝ) : Real.Angle)

/-- The Cartesian unit vector corresponding to a direction from positive `x`. -/
def directionUnitVector (direction : Real.Angle) : PlanarVector :=
  Real.Angle.cos direction • xHat + Real.Angle.sin direction • yHat

/-! ## Physical roles and primary-image vocabulary -/

/-- The two horizontal agents exerting forces on the barge. -/
inductive ForceSource where
  | horseTow
  | water
  deriving DecidableEq, Fintype, Repr

/-- Physical objects visible in the supplied primary bitmap. -/
inductive FigureObject where
  | barge
  | canalWater
  | towRope
  | horse
  deriving DecidableEq, Fintype, Repr

/-- Literal geometric annotations visible in the supplied primary bitmap. -/
inductive FigureAnnotation where
  | thetaArc
  | thetaLabel
  | horizontalReferenceRay
  deriving DecidableEq, Fintype, Repr

/-- The two visibly distinguished endpoints of the tow rope. -/
inductive RopeEndpoint where
  | bargeBow
  | horseHarness
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from image `760.png`.  These fields record
only visible objects and geometry; no water-force direction or answer value is
stored in the figure.
-/
structure SuppliedCanalFigure where
  showsObject : FigureObject → Bool
  showsAnnotation : FigureAnnotation → Bool
  ropeEndpointShown : RopeEndpoint → Bool
  bargeLongAxisHorizontal : Bool
  referenceRayPointsRight : Bool
  ropeRisesAboveReferenceRay : Bool
  thetaArcBetweenRopeAndReference : Bool
  waterFlowMarksAroundBarge : Bool
  containsWaterForceDirectionAnswer : Bool

/-!
Independent quantities in the barge experiment.  In particular, the water
force and its direction are not defined from a displayed answer; they are
constrained only by the general laws below.
-/
structure CanalBargeSetup where
  bargeMass : MassQuantity
  bargeAcceleration : PlanarAccelerationQuantity
  forceOnBarge : ForceSource → PlanarForceQuantity
  forceDirectionFromPositiveX : ForceSource → Real.Angle
  directionOfMotionFromPositiveX : Real.Angle
  figure : SuppliedCanalFigure

/-! ## Data, figure evidence, and governing laws -/

/-- Numerical and directional data explicitly supplied by the problem. -/
structure MatchesProblemReadouts (setup : CanalBargeSetup) : Prop where
  towForceMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.forceOnBarge .horseTow) = 7900
  towDirectionEighteenDegrees :
    setup.forceDirectionFromPositiveX .horseTow = angleFromDegrees 18
  bargeMassKilograms : massInKilograms setup.bargeMass = 9500
  accelerationMagnitudeMetersPerSecondSquared :
    accelerationMagnitudeInMetersPerSecondSquared setup.bargeAcceleration =
      3 / 25
  motionAlongPositiveX :
    setup.directionOfMotionFromPositiveX = angleFromDegrees 0

/-!
Primary-image evidence.  The auxiliary caption's alleged anchor is omitted:
the right endpoint is visibly held by the horse, and the rope rises above the
right-pointing horizontal reference ray.
-/
structure MatchesPrimaryCanalFigure (setup : CanalBargeSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyAnnotationShown :
    ∀ annotation, setup.figure.showsAnnotation annotation = true
  bothRopeEndpointsShown :
    ∀ endpoint, setup.figure.ropeEndpointShown endpoint = true
  bargeIsHorizontal : setup.figure.bargeLongAxisHorizontal = true
  referencePointsRight : setup.figure.referenceRayPointsRight = true
  ropeAboveReference : setup.figure.ropeRisesAboveReferenceRay = true
  thetaBetweenRays : setup.figure.thetaArcBetweenRopeAndReference = true
  waterFlowVisible : setup.figure.waterFlowMarksAroundBarge = true
  noAnswerPrinted : setup.figure.containsWaterForceDirectionAnswer = false

/-- Positivity conditions selecting the physical, nondegenerate setup. -/
structure HasPhysicalBargeParameters (setup : CanalBargeSetup) : Prop where
  massPositive : 0 < massInKilograms setup.bargeMass
  accelerationMagnitudePositive :
    0 < accelerationMagnitudeInMetersPerSecondSquared setup.bargeAcceleration
  towForceMagnitudePositive :
    0 < forceMagnitudeInNewtons (setup.forceOnBarge .horseTow)
  waterForceMagnitudePositive :
    0 < forceMagnitudeInNewtons (setup.forceOnBarge .water)

/-!
Because the barge accelerates straight along its positive direction of motion,
the acceleration vector is its stated magnitude times the corresponding unit
direction.  This is a kinematic modeling relation, not a water-force answer.
-/
structure SatisfiesStraightLineKinematics (setup : CanalBargeSetup) : Prop where
  accelerationAlongMotion :
    accelerationInMetersPerSecondSquared setup.bargeAcceleration =
      accelerationMagnitudeInMetersPerSecondSquared setup.bargeAcceleration •
        directionUnitVector setup.directionOfMotionFromPositiveX

/-!
Each applied force decomposes into its magnitude and direction relative to
positive `x`.  The law is stated in every coherent unit system and does not
assign either force a special numerical direction.
-/
structure SatisfiesPlanarForceDirectionLaw (setup : CanalBargeSetup) : Prop where
  forceHasStatedDirection :
    ∀ (units : UnitChoices) (source : ForceSource),
      planarVectorReadout units (setup.forceOnBarge source) =
        ‖planarVectorReadout units (setup.forceOnBarge source)‖ •
          directionUnitVector (setup.forceDirectionFromPositiveX source)

/-!
Newton's second law in the horizontal canal plane.  The water force here is
the total horizontal force exerted by the surrounding water; vertical weight
and buoyancy are outside this planar balance.  No direction answer is present.
-/
structure SatisfiesBargeNewtonsSecondLaw (setup : CanalBargeSetup) : Prop where
  horizontalForceBalance :
    ∀ units : UnitChoices,
      planarVectorReadout units (setup.forceOnBarge .horseTow) +
          planarVectorReadout units (setup.forceOnBarge .water) =
        nonnegativeReadout units setup.bargeMass •
          planarVectorReadout units setup.bargeAcceleration

/-! ## Derived components and displayed direction choices -/

/-- Labels of the four direction choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree readout printed beside each displayed answer label. -/
def displayedDirectionDegrees : AnswerChoice → ℝ
  | .A => 188
  | .B => 194
  | .C => 201
  | .D => 209

/-- The dataset's recorded answer label. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is strictly closer on the angle circle than every alternative. -/
def IsUniqueClosestDisplayedDirection
    (direction : Real.Angle) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ choice →
      dist direction (angleFromDegrees (displayedDirectionDegrees choice)) <
        dist direction (angleFromDegrees (displayedDirectionDegrees other))

/-!
Resolving Newton's second law into the figure's two axes gives the exact SI
components of the unknown water force.  This is a derived lemma, not a premise
field; in particular its negative `y` component is not figure input.
-/
lemma waterForceComponents
    (setup : CanalBargeSetup)
    (_data : MatchesProblemReadouts setup)
    (_kinematics : SatisfiesStraightLineKinematics setup)
    (_directions : SatisfiesPlanarForceDirectionLaw setup)
    (_newton : SatisfiesBargeNewtonsSecondLaw setup) :
    forceVectorInNewtons (setup.forceOnBarge .water) xAxis =
        1140 - 7900 * Real.Angle.cos (angleFromDegrees 18) ∧
      forceVectorInNewtons (setup.forceOnBarge .water) yAxis =
        -(7900 * Real.Angle.sin (angleFromDegrees 18)) := by
  have hTow :=
    _directions.forceHasStatedDirection UnitChoices.SI ForceSource.horseTow
  change
    forceVectorInNewtons (setup.forceOnBarge .horseTow) =
      forceMagnitudeInNewtons (setup.forceOnBarge .horseTow) •
        directionUnitVector (setup.forceDirectionFromPositiveX .horseTow)
    at hTow
  rw [_data.towForceMagnitudeNewtons, _data.towDirectionEighteenDegrees] at hTow
  have hAcceleration := _kinematics.accelerationAlongMotion
  rw [_data.accelerationMagnitudeMetersPerSecondSquared,
    _data.motionAlongPositiveX] at hAcceleration
  have hBalance := _newton.horizontalForceBalance UnitChoices.SI
  change
    forceVectorInNewtons (setup.forceOnBarge .horseTow) +
        forceVectorInNewtons (setup.forceOnBarge .water) =
      massInKilograms setup.bargeMass •
        accelerationInMetersPerSecondSquared setup.bargeAcceleration
    at hBalance
  rw [_data.bargeMassKilograms, hTow, hAcceleration] at hBalance
  constructor
  · have hx := congrArg (fun v : PlanarVector => v xAxis) hBalance
    norm_num [directionUnitVector, xHat, yHat, xAxis, yAxis, angleFromDegrees,
      degreesToRadians] at hx
    change
      (forceVectorInNewtons (setup.forceOnBarge .water)).ofLp 0 =
        1140 - 7900 * Real.cos (18 * Real.pi / 180)
    linarith
  · have hy := congrArg (fun v : PlanarVector => v yAxis) hBalance
    norm_num [directionUnitVector, xHat, yHat, xAxis, yAxis, angleFromDegrees,
      degreesToRadians] at hy
    change
      (forceVectorInNewtons (setup.forceOnBarge .water)).ofLp 1 =
        -(7900 * Real.sin (18 * Real.pi / 180))
    linarith

/-!
The force balance gives a water-force direction of approximately
`200.96 degrees`, so `201 degrees` is strictly closer than the other displayed
directions.  Hence the answer is C.

Blueprint: `thm:physics:phyx_mini_0760:target`.
-/
theorem problem_phyx_mini_0760
    (setup : CanalBargeSetup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryCanalFigure setup)
    (_physical : HasPhysicalBargeParameters setup)
    (_kinematics : SatisfiesStraightLineKinematics setup)
    (_directions : SatisfiesPlanarForceDirectionLaw setup)
    (_newton : SatisfiesBargeNewtonsSecondLaw setup) :
    dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 201) <
        degreesToRadians 1 ∧
      IsUniqueClosestDisplayedDirection
        (setup.forceDirectionFromPositiveX .water) .C := by
  have hComponents :=
    waterForceComponents setup _data _kinematics _directions _newton
  have hWaterDirection :=
    _directions.forceHasStatedDirection UnitChoices.SI ForceSource.water
  change
    forceVectorInNewtons (setup.forceOnBarge .water) =
      forceMagnitudeInNewtons (setup.forceOnBarge .water) •
        directionUnitVector (setup.forceDirectionFromPositiveX .water)
    at hWaterDirection
  have hxDirection :=
    congrArg (fun v : PlanarVector => v xAxis) hWaterDirection
  have hyDirection :=
    congrArg (fun v : PlanarVector => v yAxis) hWaterDirection
  norm_num [directionUnitVector, xHat, yHat, xAxis, yAxis] at hxDirection hyDirection
  have hScaledCos :
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.cos (setup.forceDirectionFromPositiveX .water) =
        1140 - 7900 * Real.Angle.cos (angleFromDegrees 18) := by
    linarith [hComponents.1]
  have hScaledSin :
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.sin (setup.forceDirectionFromPositiveX .water) =
        -(7900 * Real.Angle.sin (angleFromDegrees 18)) := by
    linarith [hComponents.2]
  norm_num [angleFromDegrees, degreesToRadians] at hScaledCos hScaledSin
  have hEighteenRadians :
      (18 : ℝ) * Real.pi / 180 = Real.pi / 10 := by ring
  rw [hEighteenRadians] at hScaledCos hScaledSin
  have hPiUpper : Real.pi < 3.15 := Real.pi_lt_d2
  have hPiSquare : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hPiUpper Real.pi_pos.le (by norm_num)
  have hPiCube : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hPiUpper Real.pi_pos.le (by norm_num)
  have hCosEighteenLower :=
    Real.one_sub_sq_div_two_le_cos (x := Real.pi / 10)
  have hDenominatorPositive :
      0 < 7900 * Real.cos (Real.pi / 10) - 1140 := by
    nlinarith
  have hSinEighteenPositive : 0 < Real.sin (Real.pi / 10) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hMagnitudePositive :
      0 < forceMagnitudeInNewtons (setup.forceOnBarge .water) :=
    _physical.waterForceMagnitudePositive
  have hCosDirectionNegative :
      Real.Angle.cos (setup.forceDirectionFromPositiveX .water) < 0 := by
    have hProduct :
        forceMagnitudeInNewtons (setup.forceOnBarge .water) *
            Real.Angle.cos (setup.forceDirectionFromPositiveX .water) < 0 := by
      rw [hScaledCos]
      linarith
    rcases (mul_neg_iff.mp hProduct) with h | h
    · exact h.2
    · linarith
  have hSinDirectionNegative :
      Real.Angle.sin (setup.forceDirectionFromPositiveX .water) < 0 := by
    have hProduct :
        forceMagnitudeInNewtons (setup.forceOnBarge .water) *
            Real.Angle.sin (setup.forceDirectionFromPositiveX .water) < 0 := by
      rw [hScaledSin]
      nlinarith
    rcases (mul_neg_iff.mp hProduct) with h | h
    · exact h.2
    · linarith
  have hOneEighty :
      angleFromDegrees 180 = (Real.pi : Real.Angle) := by
    change (((180 : ℝ) * Real.pi / 180 : ℝ) : Real.Angle) =
      (Real.pi : Real.Angle)
    congr 1
    ring
  let offset : Real.Angle :=
    setup.forceDirectionFromPositiveX .water - angleFromDegrees 180
  have hCosOffsetPositive : 0 < Real.Angle.cos offset := by
    dsimp [offset]
    rw [hOneEighty, Real.Angle.cos_sub_pi]
    linarith
  have hSinOffsetPositive : 0 < Real.Angle.sin offset := by
    dsimp [offset]
    rw [hOneEighty, Real.Angle.sin_sub_pi]
    linarith
  have hOffsetAbs : |offset.toReal| < Real.pi / 2 :=
    Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two.mp hCosOffsetPositive
  have hOffsetPositive : 0 < offset.toReal := by
    by_contra h
    have hSinNonpositive : Real.sin offset.toReal ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
        (Real.Angle.neg_pi_lt_toReal offset).le
    rw [Real.Angle.sin_toReal] at hSinNonpositive
    linarith
  have hOffsetLtHalfPi : offset.toReal < Real.pi / 2 :=
    (abs_lt.mp hOffsetAbs).2
  have hScaledCosOffset :
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.cos offset =
        7900 * Real.cos (Real.pi / 10) - 1140 := by
    dsimp [offset]
    rw [hOneEighty, Real.Angle.cos_sub_pi]
    calc
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          -Real.Angle.cos (setup.forceDirectionFromPositiveX .water) =
        -(forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.cos (setup.forceDirectionFromPositiveX .water)) := by ring
      _ = 7900 * Real.cos (Real.pi / 10) - 1140 := by
        rw [hScaledCos]
        ring
  have hScaledSinOffset :
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.sin offset =
        7900 * Real.sin (Real.pi / 10) := by
    dsimp [offset]
    rw [hOneEighty, Real.Angle.sin_sub_pi]
    calc
      forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          -Real.Angle.sin (setup.forceDirectionFromPositiveX .water) =
        -(forceMagnitudeInNewtons (setup.forceOnBarge .water) *
          Real.Angle.sin (setup.forceDirectionFromPositiveX .water)) := by ring
      _ = 7900 * Real.sin (Real.pi / 10) := by
        rw [hScaledSin]
        ring
  have hTangentOffset :
      Real.tan offset.toReal =
        (7900 * Real.sin (Real.pi / 10)) /
          (7900 * Real.cos (Real.pi / 10) - 1140) := by
    rw [Real.Angle.tan_toReal, Real.Angle.tan_eq_sin_div_cos]
    calc
      Real.Angle.sin offset / Real.Angle.cos offset =
          (forceMagnitudeInNewtons (setup.forceOnBarge .water) *
              Real.Angle.sin offset) /
            (forceMagnitudeInNewtons (setup.forceOnBarge .water) *
              Real.Angle.cos offset) := by
                field_simp [hMagnitudePositive.ne', hCosOffsetPositive.ne']
      _ = (7900 * Real.sin (Real.pi / 10)) /
          (7900 * Real.cos (Real.pi / 10) - 1140) := by
            rw [hScaledSinOffset, hScaledCosOffset]
  have hArctangentOffset :
      Real.arctan
          ((7900 * Real.sin (Real.pi / 10)) /
            (7900 * Real.cos (Real.pi / 10) - 1140)) =
        offset.toReal :=
    Real.arctan_eq_of_tan_eq hTangentOffset
      ⟨(abs_lt.mp hOffsetAbs).1, hOffsetLtHalfPi⟩
  have hSinTwentyLower :
      Real.pi / 9 - (Real.pi / 9) ^ 3 / 4 <
        Real.sin (Real.pi / 9) :=
    Real.sin_gt_sub_cube (by positivity) (by nlinarith)
  have hSinTwoUpper :
      Real.sin (Real.pi / 90) < Real.pi / 90 :=
    Real.sin_lt (by positivity)
  have hLowAuxiliary :
      7900 * Real.sin (Real.pi / 90) <
        1140 * Real.sin (Real.pi / 9) := by
    nlinarith [Real.pi_gt_three]
  have hSinFourLower :
      Real.pi / 45 - (Real.pi / 45) ^ 3 / 4 <
        Real.sin (Real.pi / 45) :=
    Real.sin_gt_sub_cube (by positivity) (by nlinarith)
  have hSinTwentyTwoUpper :
      Real.sin (11 * Real.pi / 90) < 11 * Real.pi / 90 :=
    Real.sin_lt (by positivity)
  have hHighAuxiliary :
      1140 * Real.sin (11 * Real.pi / 90) <
        7900 * Real.sin (Real.pi / 45) := by
    nlinarith [Real.pi_gt_three]
  have hSinTwoIdentity :
      Real.sin (Real.pi / 90) =
        Real.sin (Real.pi / 9) * Real.cos (Real.pi / 10) -
          Real.cos (Real.pi / 9) * Real.sin (Real.pi / 10) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  have hSinFourIdentity :
      Real.sin (Real.pi / 45) =
        Real.sin (11 * Real.pi / 90) * Real.cos (Real.pi / 10) -
          Real.cos (11 * Real.pi / 90) * Real.sin (Real.pi / 10) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  have hLowCrossProduct :
      Real.sin (Real.pi / 9) *
          (7900 * Real.cos (Real.pi / 10) - 1140) <
        (7900 * Real.sin (Real.pi / 10)) *
          Real.cos (Real.pi / 9) := by
    linarith only [hLowAuxiliary, hSinTwoIdentity]
  have hHighCrossProduct :
      (7900 * Real.sin (Real.pi / 10)) *
          Real.cos (11 * Real.pi / 90) <
        Real.sin (11 * Real.pi / 90) *
          (7900 * Real.cos (Real.pi / 10) - 1140) := by
    linarith only [hHighAuxiliary, hSinFourIdentity]
  have hCosTwentyPositive : 0 < Real.cos (Real.pi / 9) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hCosTwentyTwoPositive : 0 < Real.cos (11 * Real.pi / 90) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hTangentTwentyLower :
      Real.tan (Real.pi / 9) <
        (7900 * Real.sin (Real.pi / 10)) /
          (7900 * Real.cos (Real.pi / 10) - 1140) := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_lt_div_iff₀ hCosTwentyPositive hDenominatorPositive).2
      hLowCrossProduct
  have hTangentTwentyTwoUpper :
      (7900 * Real.sin (Real.pi / 10)) /
          (7900 * Real.cos (Real.pi / 10) - 1140) <
        Real.tan (11 * Real.pi / 90) := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_lt_div_iff₀ hDenominatorPositive hCosTwentyTwoPositive).2
      hHighCrossProduct
  have hTwentyMem :
      -(Real.pi / 2) < Real.pi / 9 ∧ Real.pi / 9 < Real.pi / 2 := by
    constructor <;> linarith only [Real.pi_pos]
  have hTwentyTwoMem :
      -(Real.pi / 2) < 11 * Real.pi / 90 ∧
        11 * Real.pi / 90 < Real.pi / 2 := by
    constructor <;> linarith only [Real.pi_pos]
  have hOffsetLower : Real.pi / 9 < offset.toReal := by
    calc
      Real.pi / 9 =
          Real.arctan (Real.tan (Real.pi / 9)) :=
        (Real.arctan_tan hTwentyMem.1 hTwentyMem.2).symm
      _ < Real.arctan
          ((7900 * Real.sin (Real.pi / 10)) /
            (7900 * Real.cos (Real.pi / 10) - 1140)) :=
        Real.arctan_strictMono hTangentTwentyLower
      _ = offset.toReal := hArctangentOffset
  have hOffsetUpper : offset.toReal < 11 * Real.pi / 90 := by
    calc
      offset.toReal =
          Real.arctan
            ((7900 * Real.sin (Real.pi / 10)) /
              (7900 * Real.cos (Real.pi / 10) - 1140)) :=
        hArctangentOffset.symm
      _ < Real.arctan (Real.tan (11 * Real.pi / 90)) :=
        Real.arctan_strictMono hTangentTwentyTwoUpper
      _ = 11 * Real.pi / 90 :=
        Real.arctan_tan hTwentyTwoMem.1 hTwentyTwoMem.2
  have hThetaRepresentative :
      setup.forceDirectionFromPositiveX .water =
        ((offset.toReal + Real.pi : ℝ) : Real.Angle) := by
    calc
      setup.forceDirectionFromPositiveX .water =
          offset + angleFromDegrees 180 := by
            dsimp [offset]
            abel
      _ = (offset.toReal : Real.Angle) + (Real.pi : Real.Angle) := by
        rw [hOneEighty, Real.Angle.coe_toReal]
      _ = ((offset.toReal + Real.pi : ℝ) : Real.Angle) :=
        (Real.Angle.coe_add _ _).symm
  have hTwoHundredOneRepresentative :
      angleFromDegrees 201 =
        ((7 * Real.pi / 60 + Real.pi : ℝ) : Real.Angle) := by
    change (((201 : ℝ) * Real.pi / 180 : ℝ) : Real.Angle) =
      ((7 * Real.pi / 60 + Real.pi : ℝ) : Real.Angle)
    congr 1
    ring
  have hOffsetError :
      |offset.toReal - 7 * Real.pi / 60| < Real.pi / 180 := by
    rw [abs_lt]
    constructor <;>
      linarith only [hOffsetLower, hOffsetUpper, Real.pi_pos]
  have hOffsetErrorPeriod :
      |offset.toReal - 7 * Real.pi / 60| ≤ |2 * Real.pi| / 2 := by
    refine hOffsetError.le.trans ?_
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    linarith only [Real.pi_pos]
  have hDistance :
      dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 201) <
        degreesToRadians 1 := by
    rw [hThetaRepresentative, hTwoHundredOneRepresentative, dist_eq_norm,
      ← Real.Angle.coe_sub]
    have hNorm :
        ‖(((offset.toReal + Real.pi) -
            (7 * Real.pi / 60 + Real.pi) : ℝ) : Real.Angle)‖ =
          |(offset.toReal + Real.pi) -
            (7 * Real.pi / 60 + Real.pi)| := by
      apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi)
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
      convert hOffsetErrorPeriod using 1 <;> ring
    rw [hNorm]
    have hDifference :
        (offset.toReal + Real.pi) -
            (7 * Real.pi / 60 + Real.pi) =
          offset.toReal - 7 * Real.pi / 60 := by ring
    rw [hDifference]
    simpa [degreesToRadians] using hOffsetError
  have hDegreeDistance (a b : ℝ) (hab : |a - b| ≤ 180) :
      dist (angleFromDegrees a) (angleFromDegrees b) =
        |a - b| * Real.pi / 180 := by
    change
      dist (((a * Real.pi / 180 : ℝ) : Real.Angle))
          (((b * Real.pi / 180 : ℝ) : Real.Angle)) =
        |a - b| * Real.pi / 180
    rw [dist_eq_norm, ← Real.Angle.coe_sub]
    have hRealDifference :
        a * Real.pi / 180 - b * Real.pi / 180 =
          (a - b) * Real.pi / 180 := by ring
    have hPeriod :
        |a * Real.pi / 180 - b * Real.pi / 180| ≤
          |2 * Real.pi| / 2 := by
      rw [hRealDifference, abs_div, abs_mul,
        abs_of_pos Real.pi_pos,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      norm_num
      nlinarith only [hab, Real.pi_pos]
    have hNorm :
        ‖(((a * Real.pi / 180 - b * Real.pi / 180 : ℝ) :
          Real.Angle))‖ =
          |a * Real.pi / 180 - b * Real.pi / 180| :=
      (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi)
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2 hPeriod
    rw [hNorm, hRealDifference, abs_div, abs_mul,
      abs_of_pos Real.pi_pos]
    norm_num
  refine ⟨hDistance, ?_⟩
  intro other hOther
  cases other with
  | A =>
      change
        dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 201) <
          dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 188)
      have hSeparation := hDegreeDistance 201 188 (by norm_num)
      norm_num at hSeparation
      have hTriangle :=
        dist_triangle (angleFromDegrees 201)
          (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 188)
      rw [dist_comm (angleFromDegrees 201)
        (setup.forceDirectionFromPositiveX .water), hSeparation] at hTriangle
      have hDistance' := hDistance
      simp only [degreesToRadians] at hDistance'
      linarith only [hTriangle, hDistance', Real.pi_pos]
  | B =>
      change
        dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 201) <
          dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 194)
      have hSeparation := hDegreeDistance 201 194 (by norm_num)
      norm_num at hSeparation
      have hTriangle :=
        dist_triangle (angleFromDegrees 201)
          (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 194)
      rw [dist_comm (angleFromDegrees 201)
        (setup.forceDirectionFromPositiveX .water), hSeparation] at hTriangle
      have hDistance' := hDistance
      simp only [degreesToRadians] at hDistance'
      linarith only [hTriangle, hDistance', Real.pi_pos]
  | C =>
      exact (hOther rfl).elim
  | D =>
      change
        dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 201) <
          dist (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 209)
      have hSeparation := hDegreeDistance 201 209 (by norm_num)
      norm_num at hSeparation
      have hTriangle :=
        dist_triangle (angleFromDegrees 201)
          (setup.forceDirectionFromPositiveX .water) (angleFromDegrees 209)
      rw [dist_comm (angleFromDegrees 201)
        (setup.forceDirectionFromPositiveX .water), hSeparation] at hTriangle
      have hDistance' := hDistance
      simp only [degreesToRadians] at hDistance'
      linarith only [hTriangle, hDistance', Real.pi_pos]

end PhyXMiniProblems.ProblemPhyXMini0760
