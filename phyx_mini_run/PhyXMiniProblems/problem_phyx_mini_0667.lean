import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Radius of curvature of a highway curve

This file models the helicopter-view diagram for `phyx_mini_0667`.  The road
segment is circular, the label `d` is an arc length, and the car's compass
heading turns clockwise from due east to `35.0°` south of east.  Physical
lengths are unit-independent Physlib quantities; real numbers are used only
for scalar readouts in a stated unit and for dimensionless angles in radians.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0667

open Dimension

/-- A physical length represented independently of any particular unit choice. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical readout of a dimensionful length in SI meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Convert a scalar angle read in degrees to its radian value. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- Cardinal directions printed on the compass rose in the helicopter view. -/
inductive CardinalDirection where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Repr

/-- The two depicted positions of the car on the curved road. -/
inductive CarPosition where
  | initial
  | afterTravel
  deriving DecidableEq, Repr

/--
A dashboard-compass heading, expressed as a clockwise radian offset from a
named cardinal reference direction.  Thus a positive offset from east points
south of east in the helicopter view.
-/
structure CompassHeading where
  referenceDirection : CardinalDirection
  clockwiseOffsetRadians : ℝ

/-- The dashboard reading for a car heading due east. -/
def dueEastHeading : CompassHeading where
  referenceDirection := .east
  clockwiseOffsetRadians := 0

/-- A heading through `angleRadians` clockwise from east, i.e. south of east. -/
def southOfEastHeading (angleRadians : ℝ) : CompassHeading where
  referenceDirection := .east
  clockwiseOffsetRadians := angleRadians

/-- Qualitative road shapes distinguished by the physical scenario. -/
inductive RoadShape where
  | circularArc
  | other
  deriving DecidableEq, Repr

/--
The labels and qualitative features visible in the helicopter-view figure.
`distanceArrow` is the double-headed arrow labelled `d`, while
`thetaArrowDegrees` is the angle label beside the dashed eastward line.
-/
structure HighwayCurveDiagram where
  roadShape : RoadShape
  carHeading : CarPosition → CompassHeading
  distanceArrow : LengthQuantity
  thetaArrowDegrees : ℝ
  compassRoseShows : CardinalDirection → Bool

/--
The circular-curve quantities used by the physical model.  The curvature
radius is an unknown physical length; no requested numerical radius is stored
in this setup.
-/
structure HighwayCurveSetup where
  diagram : HighwayCurveDiagram
  traveledArcLength : LengthQuantity
  curvatureRadius : LengthQuantity
  sweptCentralAngleRadians : ℝ

/--
Problem statement and figure readouts.  These identify `d` with the traveled
arc, record `840 m` and `35.0°`, and formalize the two compass readings.
-/
structure MatchesProblemAndFigure (setup : HighwayCurveSetup) : Prop where
  curveIsCircular : setup.diagram.roadShape = .circularArc
  distanceArrowIsTraveledArc :
    setup.diagram.distanceArrow = setup.traveledArcLength
  distanceArrowMeters : lengthInMeters setup.diagram.distanceArrow = 840
  thetaArrowDegrees : setup.diagram.thetaArrowDegrees = 35.0
  initialHeadingDueEast :
    setup.diagram.carHeading .initial = dueEastHeading
  finalHeadingSouthOfEast :
    setup.diagram.carHeading .afterTravel =
      southOfEastHeading
        (degreesToRadians setup.diagram.thetaArrowDegrees)
  compassRoseShowsCardinalDirections :
    ∀ direction, setup.diagram.compassRoseShows direction = true

/-- Positivity and minor-arc conditions selecting the depicted physical branch. -/
structure HasPhysicalCurveParameters (setup : HighwayCurveSetup) : Prop where
  arcLengthPositive : 0 < lengthInMeters setup.traveledArcLength
  radiusPositive : 0 < lengthInMeters setup.curvatureRadius
  centralAnglePositive : 0 < setup.sweptCentralAngleRadians
  centralAngleIsMinor : setup.sweptCentralAngleRadians < Real.pi

/--
For a circular path, the change of tangent heading equals the swept central
angle.  Clockwise offsets are used because the car turns southward from east.
-/
structure SatisfiesCircularTangentGeometry
    (setup : HighwayCurveSetup) : Prop where
  tangentTurningLaw :
    setup.sweptCentralAngleRadians =
      (setup.diagram.carHeading .afterTravel).clockwiseOffsetRadians -
        (setup.diagram.carHeading .initial).clockwiseOffsetRadians

/--
The circular-arc law `d = r θ`, imposed in every unit choice.  The angle is a
dimensionless radian scalar, so this equation is dimensionally coherent.
-/
structure SatisfiesCircularArcLengthLaw
    (setup : HighwayCurveSetup) : Prop where
  arcLengthLaw :
    ∀ units : UnitChoices,
      (setup.traveledArcLength units).val =
        (setup.curvatureRadius units).val *
          setup.sweptCentralAngleRadians

/-- The four radius choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter readout printed beside each multiple-choice answer. -/
def answerRadiusMeters : AnswerChoice → ℝ
  | .A => 2150
  | .B => 690
  | .C => 1380
  | .D => 1090

/-- Agreement with a radius displayed to the nearest ten meters. -/
def MatchesAnswerToNearestTenMeters
    (radius : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters radius - answerRadiusMeters choice| ≤ 5

/--
The circular-arc law determines the radius from a nonzero swept angle by
`r = d / θ`.  This is a derived relation rather than a figure readout.
-/
lemma curvatureRadius_eq_arcLength_div_centralAngle
    (setup : HighwayCurveSetup)
    (arcLaw : SatisfiesCircularArcLengthLaw setup)
    (centralAngle_ne_zero : setup.sweptCentralAngleRadians ≠ 0) :
    lengthInMeters setup.curvatureRadius =
      lengthInMeters setup.traveledArcLength /
        setup.sweptCentralAngleRadians := by
  apply (eq_div_iff centralAngle_ne_zero).2
  simpa [lengthInMeters] using
    (arcLaw.arcLengthLaw UnitChoices.SI).symm

/--
After an `840 m` circular arc changes the car's heading by `35.0°`, the radius
of curvature is exactly `4320 / π` meters.  This rounds to `1.38 × 10^3 m`,
answer choice C.

Blueprint: `thm:physics:phyx_mini_0667:target`.
-/
theorem problem_phyx_mini_0667
    (setup : HighwayCurveSetup)
    (_figure : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalCurveParameters setup)
    (_tangentGeometry : SatisfiesCircularTangentGeometry setup)
    (_arcLaw : SatisfiesCircularArcLengthLaw setup) :
    lengthInMeters setup.curvatureRadius = 4320 / Real.pi ∧
      MatchesAnswerToNearestTenMeters setup.curvatureRadius .C := by
  have hArcLength : lengthInMeters setup.traveledArcLength = 840 := by
    rw [← _figure.distanceArrowIsTraveledArc]
    exact _figure.distanceArrowMeters
  have hCentralAngle :
      setup.sweptCentralAngleRadians = 7 * Real.pi / 36 := by
    rw [_tangentGeometry.tangentTurningLaw,
      _figure.finalHeadingSouthOfEast, _figure.initialHeadingDueEast,
      _figure.thetaArrowDegrees]
    norm_num [southOfEastHeading, dueEastHeading, degreesToRadians]
    all_goals ring
  have hCentralAngleNe : setup.sweptCentralAngleRadians ≠ 0 := by
    exact ne_of_gt _physical.centralAnglePositive
  have hRadius :=
    curvatureRadius_eq_arcLength_div_centralAngle
      setup _arcLaw hCentralAngleNe
  have hRadiusExact :
      lengthInMeters setup.curvatureRadius = 4320 / Real.pi := by
    rw [hArcLength, hCentralAngle] at hRadius
    calc
      lengthInMeters setup.curvatureRadius =
          840 / (7 * Real.pi / 36) := hRadius
      _ = 4320 / Real.pi := by
        field_simp [Real.pi_ne_zero]
        all_goals ring
  refine ⟨hRadiusExact, ?_⟩
  rw [MatchesAnswerToNearestTenMeters, hRadiusExact]
  norm_num [answerRadiusMeters]
  have sin_lt {x : ℝ} (h : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with h' | h'
    · exact (Real.sin_le_one x).trans_lt h'
    have hx : |x| = x := abs_of_nonneg h.le
    have hs :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [sub_le_iff_le_add', hx] at hs
    apply hs.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos,
      div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have pi_gt_sqrtTwoAddSeries (n : ℕ) :
      2 ^ (n + 1) *
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have h :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 *
            2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply sin_lt
        apply div_pos Real.pi_pos
      all_goals apply pow_pos
      all_goals norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀,
      mul_comm]
    simp
  have pi_lower_bound_start (n : ℕ) {a : ℝ}
      (h :
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
          (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries n)
    rw [mul_comm]
    refine
      (div_le_iff₀ (pow_pos (by simp) _)).mp
        (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
  have sqrtTwoAddSeries_step_up
      (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    apply le_trans _ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left
        (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have hPiLower : (3.12 : ℝ) < Real.pi := by
    apply pi_lower_bound_start 2
    refine
      sqrtTwoAddSeries_step_up 99 70 ?_
        (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrtTwoAddSeries_step_up 9239 5000 ?_
        (by norm_num) (by norm_num) (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    all_goals norm_num
  have sin_gt_sub_cube {x : ℝ}
      (h : 0 < x) (h' : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have hx : |x| = x := abs_of_nonneg h.le
    have hs :=
      neg_le_of_abs_le
        (Real.sin_bound (show |x| ≤ 1 by rwa [hx]))
    rw [le_sub_iff_add_le, hx] at hs
    refine lt_of_lt_of_le ?_ hs
    have hdiff :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 =
          x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add,
      sub_lt_sub_iff_left, ← lt_sub_iff_add_lt', hdiff]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num)
      (pow_pos h 3)
    apply pow_le_pow_of_le_one h.le h'
    simp
  have pi_lt_sqrtTwoAddSeries (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) *
            Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have h :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp),
        ← Real.sin_pi_over_two_pow_succ,
        ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <|
            sin_gt_sub_cube (by positivity) <|
              div_le_one_of_le₀
                (by
                  calc
                    Real.pi ≤ 4 := Real.pi_le_four
                    _ = 2 ^ (0 + 2) := by norm_num
                    _ ≤ 2 ^ (n + 2) := by
                      gcongr <;> norm_num)
                (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num,
      ← pow_mul, div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀,
      eq_comm, mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm,
        add_comm n, add_assoc, mul_comm n]
    all_goals norm_num
  have pi_upper_bound_start (n : ℕ) {a : ℝ}
      (h :
        (2 : ℝ) -
            ((a - 1 / (4 : ℝ) ^ n) /
              (2 : ℝ) ^ (n + 1)) ^ 2 ≤
          Real.sqrtTwoAddSeries
            ((0 : ℕ) / (1 : ℕ)) n)
      (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀',
      Real.sqrt_le_left, sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact
        div_nonneg (sub_nonneg.2 h₂)
          (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have sqrtTwoAddSeries_step_down
      (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow,
      add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
      div_le_div_iff₀ (pow_pos hb' _) hd']
    exact_mod_cast h
  have hPiUpper : Real.pi < (3.1418 : ℝ) := by
    apply pi_upper_bound_start 7
    · refine
        sqrtTwoAddSeries_step_down 4756 3363 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 14965 8099 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 21183 10799 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 49188 24713 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 43947 22000 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 235667 117869 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_down 624137 312092 ?_
          (by norm_num) (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      all_goals norm_num
    · norm_num
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ Real.pi_pos]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ Real.pi_pos]
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0667
