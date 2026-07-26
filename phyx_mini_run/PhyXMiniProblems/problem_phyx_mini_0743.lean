import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0743

open Dimension

/-!
# Human-cannonball range over three Ferris wheels

Emanuel Zacchini is launched from a cannon with speed `26.5 m/s` at an angle
of `53.0°`.  The launch point and the center of the catching net are both
`3.0 m` above the ground.  The primary image also shows three `18 m` Ferris
wheels, with the first wheel `23 m` horizontally from the launch point.  Air
drag is neglected.

Physical lengths, durations, speed, and gravitational acceleration are
represented by unit-independent Physlib quantities.  Real numbers occur only
as coherent SI readouts, dimensionless schematic coordinates, trigonometric
values, and displayed answer-choice values.

Assumption/target split:

* governing laws: uniform horizontal motion and constant downward vertical
  acceleration, together with arrival at the net center;
* previous-part results: none;
* figure/data readouts: `26.5 m/s`, `53.0°`, equal `3.0 m` launch and net
  heights, three `18 m` wheels, the first-wheel distance `23 m`, and standard
  near-Earth gravity;
* target conclusions: the ideal-model range, its agreement with `69 m` to the
  displayed whole-metre precision, and selection of answer choice C.

The net distance is an independent field of the setup.  It is not defined
from the answer key or fixed to `69` by any premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `length * time⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional physical coordinate or displacement. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Metre readout of a signed coordinate. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Second readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Convert a degree readout into a physical angle modulo `2π`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-image vocabulary -/

/-- The idealization named in the prose. -/
inductive ProjectileModel where
  | uniformGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- The three distinct Ferris wheels crossed from left to right. -/
inductive FerrisWheel where
  | first
  | second
  | third
  deriving DecidableEq, Fintype, Repr

/-- Named physical objects visible in image `743.png`. -/
inductive FigureObject where
  | cannonAndRamp
  | humanCannonball
  | ferrisWheel (wheel : FerrisWheel)
  | catchingNet
  deriving DecidableEq, Fintype, Repr

/-- Numerical and symbolic labels printed in the primary image. -/
inductive FigureLabel where
  | initialSpeedVZero
  | launchAngleThetaZero
  | launchHeightThreeMeters
  | wheelHeightEighteenMeters
  | firstWheelDistanceTwentyThreeMeters
  | netHeightThreeMeters
  | rangeR
  deriving DecidableEq, Fintype, Repr

/-- Schematic points needed to retain the spatial relations in the image. -/
inductive FigureAnchor where
  | launchGroundProjection
  | launchPoint
  | wheelBase (wheel : FerrisWheel)
  | wheelTop (wheel : FerrisWheel)
  | netGroundProjection
  | netCenter
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and schematic-coordinate evidence from the primary raster.
Coordinates are dimensionless drawing coordinates, not measured lengths.
-/
structure HumanCannonballFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  horizontalCoordinate : FigureAnchor → ℝ
  verticalCoordinate : FigureAnchor → ℝ
  showsParabolicTrajectory : Bool
  trajectoryStartsAtLaunchPoint : Bool
  trajectoryEndsAtNetCenter : Bool
  rangeArrowStartsAtLaunchProjection : Bool
  rangeArrowEndsAtNetProjection : Bool

/-- A physical point in the vertical plane of the flight. -/
structure PlanarPosition where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-!
Independent physical quantities and observables for the cannonball flight.
The horizontal net distance labelled `R` is deliberately an unconstrained
physical field; the governing laws below relate it to the trajectory.
-/
structure HumanCannonballSetup where
  model : ProjectileModel
  launchSpeed : DimSpeed
  launchAngle : Real.Angle
  gravitationalAcceleration : AccelerationQuantity
  launchHeight : LengthQuantity
  netCenterHeight : LengthQuantity
  ferrisWheelHeight : FerrisWheel → LengthQuantity
  ferrisWheelHorizontalDistance : FerrisWheel → LengthQuantity
  netCenterHorizontalDistance : LengthQuantity
  flightTime : TimeQuantity
  positionAt : TimeQuantity → PlanarPosition
  figure : HumanCannonballFigure

/-! ## Figure evidence, stated readouts, and admissibility -/

/-!
Primary-image evidence.  It retains all named objects and labels, the equal
schematic heights of launch and net center, vertical wheel towers, and the
left-to-right ordering.  It contains no numerical readout for `R`.
-/
structure MatchesPrimaryFigure (setup : HumanCannonballSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  parabolicTrajectoryShown : setup.figure.showsParabolicTrajectory = true
  trajectoryStartsAtLaunch : setup.figure.trajectoryStartsAtLaunchPoint = true
  trajectoryEndsAtNet : setup.figure.trajectoryEndsAtNetCenter = true
  rangeArrowStartsAtLaunch :
    setup.figure.rangeArrowStartsAtLaunchProjection = true
  rangeArrowEndsAtNet : setup.figure.rangeArrowEndsAtNetProjection = true
  launchPointAboveItsGroundProjection :
    setup.figure.verticalCoordinate .launchGroundProjection <
      setup.figure.verticalCoordinate .launchPoint
  netCenterAboveItsGroundProjection :
    setup.figure.verticalCoordinate .netGroundProjection <
      setup.figure.verticalCoordinate .netCenter
  launchAndNetCenterDrawnAtSameHeight :
    setup.figure.verticalCoordinate .launchPoint =
      setup.figure.verticalCoordinate .netCenter
  eachWheelDrawnVertically : ∀ wheel,
    setup.figure.horizontalCoordinate (.wheelBase wheel) =
      setup.figure.horizontalCoordinate (.wheelTop wheel)
  eachWheelTopAboveItsBase : ∀ wheel,
    setup.figure.verticalCoordinate (.wheelBase wheel) <
      setup.figure.verticalCoordinate (.wheelTop wheel)
  launchIsLeftOfFirstWheel :
    setup.figure.horizontalCoordinate .launchPoint <
      setup.figure.horizontalCoordinate (.wheelBase .first)
  wheelsDrawnLeftToRight :
    setup.figure.horizontalCoordinate (.wheelBase .first) <
        setup.figure.horizontalCoordinate (.wheelBase .second) ∧
      setup.figure.horizontalCoordinate (.wheelBase .second) <
        setup.figure.horizontalCoordinate (.wheelBase .third)
  thirdWheelIsLeftOfNet :
    setup.figure.horizontalCoordinate (.wheelBase .third) <
      setup.figure.horizontalCoordinate .netCenter

/-- Numerical quantities stated in the prose or printed in the figure. -/
structure MatchesProblemReadouts (setup : HumanCannonballSetup) : Prop where
  idealProjectileModel : setup.model = .uniformGravityNegligibleDrag
  launchSpeedMetersPerSecond :
    speedInMetersPerSecond setup.launchSpeed = 53 / 2
  launchAngleDegrees : setup.launchAngle = degrees 53
  launchHeightMeters : lengthInMeters setup.launchHeight = 3
  netCenterHeightMeters : lengthInMeters setup.netCenterHeight = 3
  firstWheelDistanceMeters :
    lengthInMeters (setup.ferrisWheelHorizontalDistance .first) = 23
  eachWheelHeightMeters : ∀ wheel,
    lengthInMeters (setup.ferrisWheelHeight wheel) = 18

/-- Standard near-Earth gravitational acceleration used by the answer key. -/
structure UsesStandardNearEarthGravity
    (setup : HumanCannonballSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-!
Positivity, the upward/rightward launch branch, and the physical ordering of
the three wheels and net.  These conditions constrain geometry but do not
assign the requested range a numerical value.
-/
structure HasPhysicalCannonballParameters
    (setup : HumanCannonballSetup) : Prop where
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  flightTimePositive : 0 < timeInSeconds setup.flightTime
  launchHeightPositive : 0 < lengthInMeters setup.launchHeight
  netCenterHeightPositive : 0 < lengthInMeters setup.netCenterHeight
  eachWheelHeightPositive : ∀ wheel,
    0 < lengthInMeters (setup.ferrisWheelHeight wheel)
  eachWheelDistancePositive : ∀ wheel,
    0 < lengthInMeters (setup.ferrisWheelHorizontalDistance wheel)
  netDistancePositive :
    0 < lengthInMeters setup.netCenterHorizontalDistance
  launchPointsRight : 0 < Real.Angle.cos setup.launchAngle
  launchPointsUp : 0 < Real.Angle.sin setup.launchAngle
  wheelDistancesOrdered :
    lengthInMeters (setup.ferrisWheelHorizontalDistance .first) <
        lengthInMeters (setup.ferrisWheelHorizontalDistance .second) ∧
      lengthInMeters (setup.ferrisWheelHorizontalDistance .second) <
        lengthInMeters (setup.ferrisWheelHorizontalDistance .third)
  netLiesBeyondThirdWheel :
    lengthInMeters (setup.ferrisWheelHorizontalDistance .third) <
      lengthInMeters setup.netCenterHorizontalDistance

/-! ## Governing projectile and clearance relations -/

/-!
The no-drag, constant-gravity projectile equations in coherent SI readouts.
The final two fields identify the positive flight-time trajectory point with
the net center.  No field contains `69`, an answer label, or the eliminated
level-flight range formula.
-/
structure SatisfiesIdealProjectileMotion
    (setup : HumanCannonballSetup) : Prop where
  uniformHorizontalMotion : ∀ time : TimeQuantity,
    signedLengthInMeters (setup.positionAt time).horizontal =
      speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle * timeInSeconds time
  constantGravityVerticalMotion : ∀ time : TimeQuantity,
    signedLengthInMeters (setup.positionAt time).vertical =
      lengthInMeters setup.launchHeight +
        speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle * timeInSeconds time -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          timeInSeconds time ^ 2
  reachesNetHorizontalPosition :
    signedLengthInMeters (setup.positionAt setup.flightTime).horizontal =
      lengthInMeters setup.netCenterHorizontalDistance
  reachesNetCenterHeight :
    signedLengthInMeters (setup.positionAt setup.flightTime).vertical =
      lengthInMeters setup.netCenterHeight

/-!
The prose says Zacchini passes above all three wheels.  This observation is
kept as clearance data at genuine positive trajectory times; it neither fixes
the net distance nor asserts the requested answer.
-/
structure ClearsAllThreeFerrisWheels
    (setup : HumanCannonballSetup) : Prop where
  clearsWheel : ∀ wheel, ∃ crossingTime : TimeQuantity,
    0 < timeInSeconds crossingTime ∧
      timeInSeconds crossingTime < timeInSeconds setup.flightTime ∧
      signedLengthInMeters (setup.positionAt crossingTime).horizontal =
        lengthInMeters (setup.ferrisWheelHorizontalDistance wheel) ∧
      lengthInMeters (setup.ferrisWheelHeight wheel) <
        signedLengthInMeters (setup.positionAt crossingTime).vertical

/-! ## Derived range and displayed answer -/

/-!
Eliminating the nonzero flight time when the launch and target heights agree
gives the standard level-flight range.  This is a derived conclusion, not a
premise of the numerical answer theorem.
-/
lemma netRange_eq_levelFlightFormula
    (setup : HumanCannonballSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalCannonballParameters setup)
    (_motion : SatisfiesIdealProjectileMotion setup) :
    lengthInMeters setup.netCenterHorizontalDistance =
      speedInMetersPerSecond setup.launchSpeed ^ 2 *
          Real.Angle.sin (2 • setup.launchAngle) /
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration := by
  have hvertical :=
    _motion.constantGravityVerticalMotion setup.flightTime
  rw [_motion.reachesNetCenterHeight,
    _readouts.launchHeightMeters, _readouts.netCenterHeightMeters] at hvertical
  have ht_ne : timeInSeconds setup.flightTime ≠ 0 :=
    ne_of_gt _physical.flightTimePositive
  have hg_ne : accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration ≠ 0 :=
    ne_of_gt _physical.gravityPositive
  have hzero :
      (speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle -
        (1 / 2 : ℝ) * accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration * timeInSeconds setup.flightTime) *
        timeInSeconds setup.flightTime = 0 := by
    nlinarith
  have hrelation :
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle -
        (1 / 2 : ℝ) * accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration * timeInSeconds setup.flightTime = 0 :=
    (mul_eq_zero.mp hzero).resolve_right ht_ne
  have htime :
      timeInSeconds setup.flightTime =
        2 * speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle /
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    apply (eq_div_iff hg_ne).2
    nlinarith
  rw [← _motion.reachesNetHorizontalPosition,
    _motion.uniformHorizontalMotion, htime, two_nsmul,
    Real.Angle.sin_add]
  field_simp
  ring

/-- Exact ideal-model range from the stated speed, angle, and gravity. -/
noncomputable def computedRangeInMeters : ℝ :=
  (53 / 2 : ℝ) ^ 2 * Real.Angle.sin (2 • degrees 53) / (49 / 5 : ℝ)

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-metre distance printed beside each answer label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 63
  | .B => 66
  | .C => 69
  | .D => 72

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed distance rounded to the nearest metre. -/
def MatchesDisplayedDistance
    (setup : HumanCannonballSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.netCenterHorizontalDistance -
      choice.distanceInMeters| ≤ 1 / 2

/-- A displayed choice is at least as close as every other printed value. -/
def IsClosestDisplayedDistance
    (setup : HumanCannonballSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |lengthInMeters setup.netCenterHorizontalDistance -
        choice.distanceInMeters| ≤
      |lengthInMeters setup.netCenterHorizontalDistance -
        other.distanceInMeters|

/-- A displayed choice is the unique closest printed value. -/
def IsUniqueClosestDisplayedDistance
    (setup : HumanCannonballSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedDistance setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedDistance setup other → other = choice

/-!
The ideal trajectory has range about `68.9 m`, so its whole-metre report is
`69 m`, answer choice C.

Blueprint: `thm:physics:phyx_mini_0743:target`.
-/
theorem problem_phyx_mini_0743
    (setup : HumanCannonballSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_readouts : MatchesProblemReadouts setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalCannonballParameters setup)
    (_motion : SatisfiesIdealProjectileMotion setup)
    (_clearance : ClearsAllThreeFerrisWheels setup) :
    lengthInMeters setup.netCenterHorizontalDistance =
        computedRangeInMeters ∧
      MatchesDisplayedDistance setup .C ∧
      IsUniqueClosestDisplayedDistance setup .C := by
  have hrange :
      lengthInMeters setup.netCenterHorizontalDistance =
        computedRangeInMeters := by
    simpa [computedRangeInMeters, _readouts.launchSpeedMetersPerSecond,
      _readouts.launchAngleDegrees,
      _gravity.gravityMetersPerSecondSquared] using
      netRange_eq_levelFlightFormula setup _readouts _physical _motion
  have hsin :
      Real.Angle.sin (2 • degrees 53) =
        Real.cos (4 * Real.pi / 45) := by
    have hangle :
        2 • degrees 53 =
          ((Real.pi / 2 + 4 * Real.pi / 45 : ℝ) : Real.Angle) := by
      rw [degrees, ← Real.Angle.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    rw [hangle, Real.Angle.sin_coe, Real.sin_add,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hsin_lower :
      (239 / 250 : ℝ) < Real.Angle.sin (2 • degrees 53) := by
    rw [hsin]
    have hspecial :
        (951 / 1000 : ℝ) < Real.cos (Real.pi / 10) ∧
          (3 / 10 : ℝ) < Real.sin (Real.pi / 10) := by
      have hcos_half := Real.cos_half (x := Real.pi / 5)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      have hsin_half := Real.sin_half_eq_sqrt (x := Real.pi / 5)
        (by positivity) (by nlinarith [Real.pi_pos])
      rw [show Real.pi / 5 / 2 = Real.pi / 10 by ring,
        Real.cos_pi_div_five] at hcos_half
      rw [show Real.pi / 5 / 2 = Real.pi / 10 by ring,
        Real.cos_pi_div_five] at hsin_half
      have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := by
        norm_num
      have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt5_lower : (559 / 250 : ℝ) < Real.sqrt 5 := by
        apply (sq_lt_sq₀ (by norm_num) hsqrt5_nonneg).mp
        nlinarith
      have hsqrt5_upper : Real.sqrt 5 < (57 / 25 : ℝ) := by
        apply (sq_lt_sq₀ hsqrt5_nonneg (by norm_num)).mp
        nlinarith
      constructor
      · rw [hcos_half]
        have hrad_nonneg :
            0 ≤ (1 + (1 + Real.sqrt 5) / 4) / 2 := by
          positivity
        have hsquare := Real.sq_sqrt hrad_nonneg
        apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
        nlinarith
      · rw [hsin_half]
        have hrad_nonneg :
            0 ≤ (1 - (1 + Real.sqrt 5) / 4) / 2 := by
          nlinarith
        have hsquare := Real.sq_sqrt hrad_nonneg
        apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
        nlinarith
    let δ : ℝ := Real.pi / 90
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_lower : (1 / 45 : ℝ) ≤ δ := by
      dsimp [δ]
      nlinarith [Real.two_le_pi]
    have hδ_upper : δ ≤ (2 / 45 : ℝ) := by
      dsimp [δ]
      nlinarith [Real.pi_le_four]
    have hδ_abs : |δ| = δ := abs_of_pos hδ_pos
    have hδ_abs_le_one : |δ| ≤ 1 := by
      rw [hδ_abs]
      norm_num at hδ_upper ⊢
      linarith
    have hδ_sq_upper : δ ^ 2 ≤ (2 / 45 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_upper 2
    have hδ_cube_upper : δ ^ 3 ≤ (2 / 45 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_upper 3
    have hδ_fourth_upper : δ ^ 4 ≤ (2 / 45 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_upper 4
    have hcos_error := Real.cos_bound hδ_abs_le_one
    have hsin_error := Real.sin_bound hδ_abs_le_one
    rw [hδ_abs] at hcos_error hsin_error
    have hcosδ : (999 / 1000 : ℝ) < Real.cos δ := by
      have hlower := (abs_le.mp hcos_error).1
      nlinarith
    have hsinδ : (1 / 50 : ℝ) < Real.sin δ := by
      have hlower := (abs_le.mp hsin_error).1
      nlinarith
    rw [show 4 * Real.pi / 45 = Real.pi / 10 - δ by
      dsimp [δ]
      ring, Real.cos_sub]
    have hprod_cos :
        (951 / 1000 : ℝ) * (999 / 1000) <
          Real.cos (Real.pi / 10) * Real.cos δ :=
      mul_lt_mul hspecial.1 hcosδ.le (by norm_num)
        (by linarith [hspecial.1])
    have hprod_sin :
        (3 / 10 : ℝ) * (1 / 50) <
          Real.sin (Real.pi / 10) * Real.sin δ :=
      mul_lt_mul hspecial.2 hsinδ.le (by norm_num)
        (by linarith [hspecial.2])
    nlinarith
  have hsin_upper :
      Real.Angle.sin (2 • degrees 53) < (969 / 1000 : ℝ) := by
    rw [hsin]
    have hmono :
        Real.cos (4 * Real.pi / 45) < Real.cos (Real.pi / 12) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hcos15_upper :
        Real.cos (Real.pi / 12) < (969 / 1000 : ℝ) := by
      rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
        Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_six, Real.sin_pi_div_six]
      have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := by
        norm_num
      have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := by
        norm_num
      have hsqrt2_upper : Real.sqrt 2 < (283 / 200 : ℝ) := by
        apply (sq_lt_sq₀ (Real.sqrt_nonneg 2) (by norm_num)).mp
        nlinarith
      have hsqrt3_upper : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
        apply (sq_lt_sq₀ (Real.sqrt_nonneg 3) (by norm_num)).mp
        nlinarith
      have hprod :
          Real.sqrt 2 * Real.sqrt 3 <
            (283 / 200 : ℝ) * (1733 / 1000) :=
        mul_lt_mul hsqrt2_upper hsqrt3_upper.le
          (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
      nlinarith
    linarith
  have hcomputed_lower : (137 / 2 : ℝ) < computedRangeInMeters := by
    rw [computedRangeInMeters]
    norm_num at hsin_lower ⊢
    linarith
  have hcomputed_upper : computedRangeInMeters < (139 / 2 : ℝ) := by
    rw [computedRangeInMeters]
    norm_num at hsin_upper ⊢
    linarith
  have hrange_lower :
      (137 / 2 : ℝ) <
        lengthInMeters setup.netCenterHorizontalDistance := by
    rw [hrange]
    exact hcomputed_lower
  have hrange_upper :
      lengthInMeters setup.netCenterHorizontalDistance <
        (139 / 2 : ℝ) := by
    rw [hrange]
    exact hcomputed_upper
  have hCerror :
      |lengthInMeters setup.netCenterHorizontalDistance - 69| ≤
        (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hAfar :
      (1 / 2 : ℝ) <
        |lengthInMeters setup.netCenterHorizontalDistance - 63| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hBfar :
      (1 / 2 : ℝ) <
        |lengthInMeters setup.netCenterHorizontalDistance - 66| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hDfar :
      (1 / 2 : ℝ) <
        |lengthInMeters setup.netCenterHorizontalDistance - 72| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hclosestC : IsClosestDisplayedDistance setup .C := by
    intro other
    cases other with
    | A =>
        simpa [AnswerChoice.distanceInMeters] using hCerror.trans hAfar.le
    | B =>
        simpa [AnswerChoice.distanceInMeters] using hCerror.trans hBfar.le
    | C => exact le_rfl
    | D =>
        simpa [AnswerChoice.distanceInMeters] using hCerror.trans hDfar.le
  refine ⟨hrange, ?_, hclosestC, ?_⟩
  · simpa [MatchesDisplayedDistance, AnswerChoice.distanceInMeters]
      using hCerror
  · intro other hclosestOther
    cases other with
    | A =>
        exfalso
        have hreverse := hclosestOther .C
        simp only [AnswerChoice.distanceInMeters] at hreverse
        linarith
    | B =>
        exfalso
        have hreverse := hclosestOther .C
        simp only [AnswerChoice.distanceInMeters] at hreverse
        linarith
    | C => rfl
    | D =>
        exfalso
        have hreverse := hclosestOther .C
        simp only [AnswerChoice.distanceInMeters] at hreverse
        linarith

end PhyXMiniProblems.ProblemPhyXMini0743
