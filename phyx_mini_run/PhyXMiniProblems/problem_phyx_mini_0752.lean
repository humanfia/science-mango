import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0752

open Dimension

/-!
# Initial speed of a volcanic bomb

A volcanic bomb is launched from the vent `A` of Mt. Fuji at `35 degrees`
above the horizontal and lands at the foot `B`.  The landing point is
`3.30 km` below the vent and `9.40 km` horizontally from it.  Aerodynamic
drag is neglected.

Lengths, durations, speeds, and gravitational acceleration are represented by
Physlib dimensionful quantities.  Real numbers occur only as coherent-SI
readouts, dimensionless trigonometric values, schematic figure coordinates,
and displayed answer values.

The launch speed is an independent physical field.  The premises constrain it
only through the general uniform-gravity projectile equations; no premise
mentions `255.5 m/s`, selects choice C, or equates the speed to the solved
closed form.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional physical displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative duration elapsed since launch. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical launch-speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre readout of a signed physical displacement. -/
def signedLengthInMeters (displacement : SignedLengthQuantity) : ℝ :=
  (displacement UnitChoices.SI).val

/-- Second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-image vocabulary -/

/-- The physical object launched by the eruption. -/
inductive ProjectileKind where
  | volcanicBomb
  deriving DecidableEq, Repr

/-- The approximation explicitly requested in the problem. -/
inductive ProjectileModel where
  | uniformGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- Named physical locations in the prose and primary image. -/
inductive PhysicalLocation where
  | ventA
  | footB
  deriving DecidableEq, Repr

/-- Distinguished points needed to transcribe the diagram's geometry. -/
inductive FigurePoint where
  | ventA
  | verticalProjectionBelowA
  | footB
  deriving DecidableEq, Fintype, Repr

/-- Physical or graphical objects visible in image `752.png`. -/
inductive FigureObject where
  | volcanoCrossSection
  | volcanicBomb
  | eruptiveStreaks
  | projectileTrajectory
  | launchVelocityArrow
  deriving DecidableEq, Fintype, Repr

/-- Text and mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | launchPointA
  | landingPointB
  | launchAngleThetaZero
  | verticalDistanceH
  | horizontalDistanceD
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and schematic-coordinate information from the raster.
The coordinates are dimensionless drawing coordinates, not physical lengths.
-/
structure MtFujiProjectileFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  horizontalCoordinate : FigurePoint → ℝ
  verticalCoordinate : FigurePoint → ℝ
  trajectoryStart : FigurePoint
  trajectoryEnd : FigurePoint
  heightArrowEndpoints : FigurePoint × FigurePoint
  distanceArrowEndpoints : FigurePoint × FigurePoint
  launchArrowPointsUpAndRight : Bool
  angleArcIsMeasuredFromHorizontal : Bool

/-!
Independent physical quantities for the launch.  The displacement functions
use an origin at vent `A`, with positive horizontal direction toward `B` and
positive vertical direction upward.  In particular, `launchSpeed` is not
defined from an answer choice or from the closed-form result.
-/
structure VolcanicBombSetup where
  projectileKind : ProjectileKind
  model : ProjectileModel
  launchLocation : PhysicalLocation
  landingLocation : PhysicalLocation
  verticalDrop : LengthQuantity
  horizontalDistance : LengthQuantity
  launchAngle : Real.Angle
  launchSpeed : SpeedQuantity
  gravitationalAcceleration : AccelerationQuantity
  flightDuration : DurationQuantity
  horizontalDisplacement : DurationQuantity → SignedLengthQuantity
  verticalDisplacement : DurationQuantity → SignedLengthQuantity
  figure : MtFujiProjectileFigure

/-! ## Figure evidence, numerical data, physical branch, and laws -/

/-!
Primary-image evidence: `A` lies vertically above the left endpoint of the
horizontal `d` arrow, `B` is at the same level as that endpoint and to its
right, the curve runs from `A` to `B`, and the launch arrow points upward and
right at the angle marked `theta_0`.
-/
structure MatchesPrimaryFigure (setup : VolcanicBombSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  ventAboveItsVerticalProjection :
    setup.figure.verticalCoordinate .verticalProjectionBelowA <
      setup.figure.verticalCoordinate .ventA
  projectionDirectlyBelowVent :
    setup.figure.horizontalCoordinate .verticalProjectionBelowA =
      setup.figure.horizontalCoordinate .ventA
  landingRightOfProjection :
    setup.figure.horizontalCoordinate .verticalProjectionBelowA <
      setup.figure.horizontalCoordinate .footB
  landingAtProjectionLevel :
    setup.figure.verticalCoordinate .footB =
      setup.figure.verticalCoordinate .verticalProjectionBelowA
  trajectoryRunsFromAToB :
    setup.figure.trajectoryStart = .ventA ∧
      setup.figure.trajectoryEnd = .footB
  heightArrowRunsFromAToProjection :
    setup.figure.heightArrowEndpoints =
      (.ventA, .verticalProjectionBelowA)
  distanceArrowRunsFromProjectionToB :
    setup.figure.distanceArrowEndpoints =
      (.verticalProjectionBelowA, .footB)
  launchArrowDirectionShown :
    setup.figure.launchArrowPointsUpAndRight = true
  angleMeasuredFromHorizontal :
    setup.figure.angleArcIsMeasuredFromHorizontal = true

/-- Convert a degree readout to Mathlib's physical angle modulo `2 * pi`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-!
The qualitative scenario and numerical readouts stated in the question.  The
kilometre data are converted to coherent-SI metre readouts.  No launch-speed
value occurs here.
-/
structure MatchesProblemDescription (setup : VolcanicBombSetup) : Prop where
  projectileIsVolcanicBomb : setup.projectileKind = .volcanicBomb
  usesRequestedIdealization : setup.model = .uniformGravityNegligibleDrag
  launchedFromVentA : setup.launchLocation = .ventA
  landsAtFootB : setup.landingLocation = .footB
  verticalDropMeters : lengthInMeters setup.verticalDrop = 3300
  horizontalDistanceMeters :
    lengthInMeters setup.horizontalDistance = 9400
  launchAngleDegrees : setup.launchAngle = degrees 35

/-!
The standard near-Earth gravitational acceleration used by the textbook
projectile model.  This calibration does not constrain the answer speed.
-/
structure UsesStandardNearEarthGravity
    (setup : VolcanicBombSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-!
Positivity and direction assumptions selecting the physical upward/rightward
branch shown in the figure.  None assigns a numerical launch speed.
-/
structure HasPhysicalProjectileParameters
    (setup : VolcanicBombSetup) : Prop where
  verticalDropPositive : 0 < lengthInMeters setup.verticalDrop
  horizontalDistancePositive :
    0 < lengthInMeters setup.horizontalDistance
  flightDurationPositive : 0 < durationInSeconds setup.flightDuration
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  launchPointsRight : 0 < Real.Angle.cos setup.launchAngle
  launchPointsUp : 0 < Real.Angle.sin setup.launchAngle

/-!
The standard no-drag projectile equations in coherent SI readouts.  Horizontal
motion is uniform; vertical motion has constant downward acceleration.  At the
positive flight duration, the bomb's displacement is `d` horizontally and
`-h` vertically, exactly encoding landing at `B` below `A`.

These are governing laws and endpoint geometry only.  They contain neither a
solved launch-speed formula nor any displayed answer value.
-/
structure SatisfiesUniformGravityProjectileLaws
    (setup : VolcanicBombSetup) : Prop where
  uniformHorizontalMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.horizontalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle * durationInSeconds duration
  verticalConstantGravityMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.verticalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle * durationInSeconds duration -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          durationInSeconds duration ^ 2
  landsAtHorizontalDistanceD :
    signedLengthInMeters
        (setup.horizontalDisplacement setup.flightDuration) =
      lengthInMeters setup.horizontalDistance
  landsVerticalDistanceHBelowA :
    signedLengthInMeters
        (setup.verticalDisplacement setup.flightDuration) =
      -lengthInMeters setup.verticalDrop

/-! ## Derived speed expression and displayed answers -/

/-!
Eliminating flight time from the two endpoint equations gives this unrounded
speed readout.  It depends only on the independent distance, angle, and gravity
fields, not on `setup.launchSpeed` and not on an answer choice.
-/
noncomputable def requiredLaunchSpeedInMetersPerSecond
    (setup : VolcanicBombSetup) : ℝ :=
  Real.sqrt
    (accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.horizontalDistance ^ 2 /
      (2 * Real.Angle.cos setup.launchAngle ^ 2 *
        (lengthInMeters setup.verticalDrop +
          lengthInMeters setup.horizontalDistance *
            (Real.Angle.sin setup.launchAngle /
              Real.Angle.cos setup.launchAngle))))

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer choice. -/
def AnswerChoice.speedMetersPerSecond : AnswerChoice → ℝ
  | .A => 471 / 2
  | .B => 491 / 2
  | .C => 511 / 2
  | .D => 531 / 2

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Absolute display error for a candidate answer speed. -/
def answerChoiceErrorMetersPerSecond
    (setup : VolcanicBombSetup) (choice : AnswerChoice) : ℝ :=
  |speedInMetersPerSecond setup.launchSpeed - choice.speedMetersPerSecond|

/-- Agreement with a speed displayed to the nearest tenth of a metre per second. -/
def MatchesDisplayedLaunchSpeed
    (setup : VolcanicBombSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMetersPerSecond setup choice ≤ (1 : ℝ) / 20

/-- The selected displayed speed is strictly closer than every other choice. -/
def IsUniqueClosestLaunchSpeedChoice
    (setup : VolcanicBombSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecond setup choice <
      answerChoiceErrorMetersPerSecond setup other

/-!
The governing equations determine the initial speed's exact unrounded SI
readout.  This conclusion is not a field of any premise structure.
-/
lemma launchSpeed_eq_requiredExpression
    (setup : VolcanicBombSetup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.launchSpeed =
      requiredLaunchSpeedInMetersPerSecond setup := by
  let v := speedInMetersPerSecond setup.launchSpeed
  let d := lengthInMeters setup.horizontalDistance
  let h := lengthInMeters setup.verticalDrop
  let g :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let t := durationInSeconds setup.flightDuration
  let c := Real.Angle.cos setup.launchAngle
  let s := Real.Angle.sin setup.launchAngle
  have hv : 0 < v := _physical.launchSpeedPositive
  have hd : 0 < d := _physical.horizontalDistancePositive
  have hh : 0 < h := _physical.verticalDropPositive
  have hg : 0 < g := _physical.gravityPositive
  have ht : 0 < t := _physical.flightDurationPositive
  have hc : 0 < c := _physical.launchPointsRight
  have hs : 0 < s := _physical.launchPointsUp
  have hx : d = v * c * t := by
    simpa [d, v, c, t] using
      (_laws.landsAtHorizontalDistanceD.symm.trans
        (_laws.uniformHorizontalMotion setup.flightDuration))
  have hy : -h = v * s * t - (1 / 2 : ℝ) * g * t ^ 2 := by
    simpa [h, v, s, g, t] using
      (_laws.landsVerticalDistanceHBelowA.symm.trans
        (_laws.verticalConstantGravityMotion setup.flightDuration))
  have hdc : d / c = v * t := by
    apply (div_eq_iff (ne_of_gt hc)).2
    nlinarith [hx]
  have hheight :
      h + d * (s / c) = h + v * s * t := by
    rw [show d * (s / c) = (d / c) * s by ring, hdc]
    ring
  have hheight_pos : 0 < h + d * (s / c) := by
    exact add_pos hh (mul_pos hd (div_pos hs hc))
  have hvertical :
      g * t ^ 2 = 2 * (h + v * s * t) := by
    nlinarith [hy]
  have hden_pos :
      0 < 2 * c ^ 2 * (h + d * (s / c)) := by
    positivity
  have hradicand :
      g * d ^ 2 / (2 * c ^ 2 * (h + d * (s / c))) = v ^ 2 := by
    apply (div_eq_iff (ne_of_gt hden_pos)).2
    calc
      g * d ^ 2 = g * (v * c * t) ^ 2 := by rw [hx]
      _ = v ^ 2 * c ^ 2 * (g * t ^ 2) := by ring
      _ = v ^ 2 * c ^ 2 * (2 * (h + v * s * t)) := by rw [hvertical]
      _ = v ^ 2 * (2 * c ^ 2 * (h + d * (s / c))) := by
        rw [hheight]
        ring
  change v = Real.sqrt
    (g * d ^ 2 / (2 * c ^ 2 * (h + d * (s / c))))
  rw [hradicand, Real.sqrt_sq_eq_abs, abs_of_pos hv]

/-!
For the stated `3.30 km`, `9.40 km`, `35 degrees`, and `9.80 m/s^2` data, the
unrounded result is approximately `255.5289 m/s`.  Thus it displays as
`255.5 m/s`, and choice C is uniquely closest among the four printed values.

Blueprint: `thm:physics:phyx_mini_0752:target`.
-/
theorem problem_phyx_mini_0752
    (setup : VolcanicBombSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.launchSpeed =
        requiredLaunchSpeedInMetersPerSecond setup ∧
      MatchesDisplayedLaunchSpeed setup .C ∧
      IsUniqueClosestLaunchSpeedChoice setup .C := by
  let v := speedInMetersPerSecond setup.launchSpeed
  let c := Real.Angle.cos setup.launchAngle
  let s := Real.Angle.sin setup.launchAngle
  let x : ℝ := 7 * Real.pi / 36
  let y : ℝ := 7 * Real.pi / 18
  let S : ℝ := Real.sin y
  let C : ℝ := Real.cos y
  have hv : 0 < v := _physical.launchSpeedPositive
  have hc : 0 < c := _physical.launchPointsRight
  have hs : 0 < s := _physical.launchPointsUp
  have hspeed :
      v = requiredLaunchSpeedInMetersPerSecond setup := by
    simpa [v] using
      launchSpeed_eq_requiredExpression setup _description _gravity
        _physical _laws
  have hcos35 : c = Real.cos x := by
    dsimp [c]
    rw [_description.launchAngleDegrees]
    simp only [degrees, Real.Angle.cos_coe]
    congr 1
    dsimp [x]
    ring
  have hsin35 : s = Real.sin x := by
    dsimp [s]
    rw [_description.launchAngleDegrees]
    simp only [degrees, Real.Angle.sin_coe]
    congr 1
    dsimp [x]
    ring
  have htwox : 2 * x = y := by
    dsimp [x, y]
    ring
  have hcos_sq : c ^ 2 = (1 + C) / 2 := by
    have hdouble := Real.cos_two_mul x
    rw [htwox] at hdouble
    change C = 2 * Real.cos x ^ 2 - 1 at hdouble
    rw [hcos35]
    nlinarith
  have hsincos : s * c = S / 2 := by
    have hdouble := Real.sin_two_mul x
    rw [htwox] at hdouble
    change S = 2 * Real.sin x * Real.cos x at hdouble
    rw [hsin35, hcos35]
    nlinarith
  have hy_pos : 0 < y := by
    dsimp [y]
    positivity
  have hy_lt_half_pi : y < Real.pi / 2 := by
    dsimp [y]
    nlinarith [Real.pi_pos]
  have hS_pos : 0 < S := by
    dsimp [S]
    exact Real.sin_pos_of_pos_of_lt_pi hy_pos
      (lt_trans hy_lt_half_pi (by nlinarith [Real.pi_pos]))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], hy_lt_half_pi⟩
  have hsin210 : Real.sin (3 * y) = -(1 / 2 : ℝ) := by
    rw [show 3 * y = Real.pi + Real.pi / 6 by
      dsimp [y]
      ring]
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi,
      Real.sin_pi_div_six, Real.cos_pi_div_six]
    ring
  have hS_cubic : 4 * S ^ 3 - 3 * S = (1 / 2 : ℝ) := by
    have htriple := Real.sin_three_mul y
    rw [hsin210] at htriple
    dsimp [S]
    nlinarith
  have hS_gt_four_fifths : (4 / 5 : ℝ) < S := by
    have hsin_mono :
        Real.sin (Real.pi / 3) < Real.sin y := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos])
        (le_of_lt hy_lt_half_pi)
        (by dsimp [y]; nlinarith [Real.pi_pos])
    rw [Real.sin_pi_div_three] at hsin_mono
    have hsqrt3_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hsqrt3_large : (8 / 5 : ℝ) < Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    linarith
  have hS_lower : (939692 / 1000000 : ℝ) < S := by
    by_contra h
    have hle : S ≤ (939692 / 1000000 : ℝ) := le_of_not_gt h
    have hfactor_positive :
        0 <
          4 * (S ^ 2 + S * (939692 / 1000000 : ℝ) +
              (939692 / 1000000 : ℝ) ^ 2) - 3 := by
      nlinarith [sq_nonneg S]
    have hfactor :
        0 ≤ ((939692 / 1000000 : ℝ) - S) *
          (4 * (S ^ 2 + S * (939692 / 1000000 : ℝ) +
              (939692 / 1000000 : ℝ) ^ 2) - 3) :=
      mul_nonneg (sub_nonneg.mpr hle) hfactor_positive.le
    nlinarith [hS_cubic]
  have hS_upper : S < (939693 / 1000000 : ℝ) := by
    by_contra h
    have hge : (939693 / 1000000 : ℝ) ≤ S := le_of_not_gt h
    have hfactor_positive :
        0 <
          4 * (S ^ 2 + S * (939693 / 1000000 : ℝ) +
              (939693 / 1000000 : ℝ) ^ 2) - 3 := by
      nlinarith [sq_nonneg S]
    have hfactor :
        0 ≤ (S - (939693 / 1000000 : ℝ)) *
          (4 * (S ^ 2 + S * (939693 / 1000000 : ℝ) +
              (939693 / 1000000 : ℝ) ^ 2) - 3) :=
      mul_nonneg (sub_nonneg.mpr hge) hfactor_positive.le
    nlinarith [hS_cubic]
  have hcircle : S ^ 2 + C ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq y
  have hC_lower : (342019 / 1000000 : ℝ) < C := by
    by_contra h
    have hle : C ≤ (342019 / 1000000 : ℝ) := le_of_not_gt h
    have hS_sq :
        S ^ 2 < (939693 / 1000000 : ℝ) ^ 2 := by
      simpa [pow_two] using
        mul_self_lt_mul_self hS_pos.le hS_upper
    have hC_sq :
        C ^ 2 ≤ (342019 / 1000000 : ℝ) ^ 2 := by
      simpa [pow_two] using
        mul_self_le_mul_self hC_pos.le hle
    nlinarith
  have hC_upper : C < (342022 / 1000000 : ℝ) := by
    by_contra h
    have hge : (342022 / 1000000 : ℝ) ≤ C := le_of_not_gt h
    have hS_sq :
        (939692 / 1000000 : ℝ) ^ 2 < S ^ 2 := by
      simpa [pow_two] using
        mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 939692 / 1000000)
          hS_lower
    have hC_sq :
        (342022 / 1000000 : ℝ) ^ 2 ≤ C ^ 2 := by
      simpa [pow_two] using
        mul_self_le_mul_self
          (by norm_num : (0 : ℝ) ≤ 342022 / 1000000) hge
    nlinarith
  have hdenominator :
      2 * c ^ 2 *
          (3300 + 9400 * (s / c)) =
        3300 * (1 + C) + 9400 * S := by
    calc
      2 * c ^ 2 * (3300 + 9400 * (s / c)) =
          2 * 3300 * c ^ 2 + 2 * 9400 * (s * c) := by
            field_simp [ne_of_gt hc]
      _ = 3300 * (1 + C) + 9400 * S := by
        rw [hcos_sq, hsincos]
        ring
  have hD_lower :
      (132617675 / 10000 : ℝ) <
        3300 * (1 + C) + 9400 * S := by
    nlinarith only [hC_lower, hS_lower]
  have hD_upper :
      3300 * (1 + C) + 9400 * S <
        (132617868 / 10000 : ℝ) := by
    nlinarith only [hC_upper, hS_upper]
  have hD_pos :
      0 < 3300 * (1 + C) + 9400 * S := by
    positivity
  have hv_sq_raw :
      v ^ 2 =
        accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.horizontalDistance ^ 2 /
          (2 * c ^ 2 *
            (lengthInMeters setup.verticalDrop +
              lengthInMeters setup.horizontalDistance * (s / c))) := by
    change v = Real.sqrt
      (accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.horizontalDistance ^ 2 /
        (2 * c ^ 2 *
          (lengthInMeters setup.verticalDrop +
            lengthInMeters setup.horizontalDistance * (s / c)))) at hspeed
    rw [hspeed, Real.sq_sqrt]
    apply div_nonneg
    · exact mul_nonneg _physical.gravityPositive.le
        (sq_nonneg (lengthInMeters setup.horizontalDistance))
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg c))
        (add_pos _physical.verticalDropPositive
          (mul_pos _physical.horizontalDistancePositive
            (div_pos hs hc))).le
  have hv_sq :
      v ^ 2 =
        ((49 / 5 : ℝ) * 9400 ^ 2) /
          (3300 * (1 + C) + 9400 * S) := by
    rw [_gravity.gravityMetersPerSecondSquared,
      _description.horizontalDistanceMeters,
      _description.verticalDropMeters] at hv_sq_raw
    rw [hdenominator] at hv_sq_raw
    exact hv_sq_raw
  have hv_product :
      v ^ 2 * (3300 * (1 + C) + 9400 * S) =
        (49 / 5 : ℝ) * 9400 ^ 2 :=
    (eq_div_iff (ne_of_gt hD_pos)).mp hv_sq
  have hv_sq_lower : (5109 / 20 : ℝ) ^ 2 < v ^ 2 := by
    by_contra h
    have hle : v ^ 2 ≤ (5109 / 20 : ℝ) ^ 2 := le_of_not_gt h
    have hproduct_le :=
      mul_le_mul hle (le_of_lt hD_upper) hD_pos.le
        (sq_nonneg (5109 / 20 : ℝ))
    norm_num at hproduct_le
    nlinarith only [hproduct_le, hv_product]
  have hv_sq_upper : v ^ 2 < (5111 / 20 : ℝ) ^ 2 := by
    by_contra h
    have hge : (5111 / 20 : ℝ) ^ 2 ≤ v ^ 2 := le_of_not_gt h
    have hproduct_le :=
      mul_le_mul hge (le_of_lt hD_lower)
        (by norm_num : (0 : ℝ) ≤ 132617675 / 10000)
        (sq_nonneg v)
    norm_num at hproduct_le
    nlinarith only [hproduct_le, hv_product]
  have hv_lower : (5109 / 20 : ℝ) < v :=
    (sq_lt_sq₀ (by norm_num) hv.le).mp hv_sq_lower
  have hv_upper : v < (5111 / 20 : ℝ) :=
    (sq_lt_sq₀ hv.le (by norm_num)).mp hv_sq_upper
  have hdisplay :
      MatchesDisplayedLaunchSpeed setup .C := by
    change |v - 511 / 2| ≤ (1 : ℝ) / 20
    rw [abs_le]
    constructor <;> linarith
  have hclosest :
      IsUniqueClosestLaunchSpeedChoice setup .C := by
    intro other hne
    change |v - 511 / 2| <
      |v - AnswerChoice.speedMetersPerSecond other|
    have hC_error : |v - 511 / 2| < (1 : ℝ) / 20 := by
      rw [abs_lt]
      constructor <;> linarith
    cases other with
    | A =>
        rw [AnswerChoice.speedMetersPerSecond]
        have hAabs : |v - 471 / 2| = v - 471 / 2 :=
          abs_of_pos (by linarith)
        rw [hAabs]
        linarith only [hC_error, hv_lower]
    | B =>
        rw [AnswerChoice.speedMetersPerSecond]
        have hBabs : |v - 491 / 2| = v - 491 / 2 :=
          abs_of_pos (by linarith)
        rw [hBabs]
        linarith only [hC_error, hv_lower]
    | C => exact (hne rfl).elim
    | D =>
        rw [AnswerChoice.speedMetersPerSecond]
        have hDabs : |v - 531 / 2| = -(v - 531 / 2) :=
          abs_of_neg (by linarith)
        rw [hDabs]
        linarith only [hC_error, hv_upper]
  exact ⟨hspeed, hdisplay, hclosest⟩

end PhyXMiniProblems.ProblemPhyXMini0752
