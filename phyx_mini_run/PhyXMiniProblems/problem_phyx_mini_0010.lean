import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

/-!
# Maximum acceptance angle of a transparent cylindrical rod

This file formalizes problem `phyx_mini_0010`. The rod diameter is a
dimensionful Physlib length. Refractive indices are dimensionless real
readouts, and the angles below are real readouts measured in radians.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0010

open CarriesDimension

/--
The three optical roles in the figure. The two air regions are kept distinct
because one borders the flat end face and the other borders the cylindrical
wall, even though their refractive-index readouts are equal in this problem.
-/
inductive OpticalRegion where
  | incidentAir
  | transparentRod
  | exteriorAir
  deriving DecidableEq, Repr

/--
The physical data carried by the horizontal cylindrical rod in the figure.
The figure label `d` is represented by a unit-independent dimensionful length.
-/
structure CylindricalRodSetup where
  /-- Figure label `d`, the diameter of the rod. -/
  diameter : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Dimensionless refractive index, separated by optical role. -/
  refractiveIndex : OpticalRegion → ℝ
  /-- The rod transmits the light rays considered in the problem. -/
  rodIsTransparent : Prop

/-- The dimensionful length whose source readout is `2.00` in micrometers. -/
noncomputable def twoMicrometers :
    Dimensionful (WithDim Dimension.L𝓭 ℝ) :=
  toDimensionful
    ({UnitChoices.SI with length := LengthUnit.micrometers} : UnitChoices) ⟨2⟩

/--
Problem and figure readouts: a transparent `2.00 μm` rod of refractive index
`1.36`, with air (index one) at both the flat entrance and the side wall.
-/
structure CylindricalRodFigureReadouts (setup : CylindricalRodSetup) : Prop where
  rod_is_transparent : setup.rodIsTransparent
  diameter_readout : setup.diameter = twoMicrometers
  refractive_indices_positive : ∀ region, 0 < setup.refractiveIndex region
  incident_air_index : setup.refractiveIndex .incidentAir = 1
  rod_index : setup.refractiveIndex .transparentRod = 1.36
  exterior_air_index : setup.refractiveIndex .exteriorAir = 1

/--
Snell's law at the flat end face. Both angles are measured from the dashed rod
axis, which is also the end-face normal.
-/
def SatisfiesEndFaceSnellLaw
    (setup : CylindricalRodSetup)
    (externalAngleRadians insideAxisAngleRadians : ℝ) : Prop :=
  setup.refractiveIndex .incidentAir * Real.sin externalAngleRadians =
    setup.refractiveIndex .transparentRod * Real.sin insideAxisAngleRadians

/--
In the axial cross-section, the normal to a cylindrical side wall is
perpendicular to the dashed rod axis. Thus these two incidence angles are
complementary.
-/
def wallIncidenceAngleRadians (insideAxisAngleRadians : ℝ) : ℝ :=
  Real.pi / 2 - insideAxisAngleRadians

/--
The critical-angle threshold for total internal reflection at the rod--air
wall. The non-strict inequality includes the limiting critical ray used to
define the largest geometrical-optics acceptance angle.
-/
def MeetsWallTotalInternalReflectionThreshold
    (setup : CylindricalRodSetup) (insideAxisAngleRadians : ℝ) : Prop :=
  setup.refractiveIndex .exteriorAir ≤
    setup.refractiveIndex .transparentRod *
      Real.sin (wallIncidenceAngleRadians insideAxisAngleRadians)

/--
An external ray is guided along the rod when it has an acute refracted ray
which obeys Snell's law and reaches every cylindrical wall at or above the TIR
threshold. The angle shown as `θ` in the figure is `externalAngleRadians`.
-/
def CanBeGuidedByTotalInternalReflection
    (setup : CylindricalRodSetup) (externalAngleRadians : ℝ) : Prop :=
  externalAngleRadians ∈ Set.Icc 0 (Real.pi / 2) ∧
    ∃ insideAxisAngleRadians ∈ Set.Icc 0 (Real.pi / 2),
      SatisfiesEndFaceSnellLaw
          setup externalAngleRadians insideAxisAngleRadians ∧
        MeetsWallTotalInternalReflectionThreshold setup insideAxisAngleRadians

/-- A guided angle which is at least every other guided external angle. -/
def IsMaximumGuidedAngle
    (setup : CylindricalRodSetup) (thetaRadians : ℝ) : Prop :=
  CanBeGuidedByTotalInternalReflection setup thetaRadians ∧
    ∀ otherThetaRadians,
      CanBeGuidedByTotalInternalReflection setup otherThetaRadians →
        otherThetaRadians ≤ thetaRadians

/-- Convert a radian readout to a degree readout. -/
def degreeReadout (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- The four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 72.2
  | .B => 65.4
  | .C => 67.2
  | .D => 60.0

/-- Agreement with a displayed one-decimal-place answer after rounding. -/
def MatchesAnswerToNearestTenth
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |degreeReadout angleRadians - answerAngleDegrees choice| ≤ 0.05

/--
For the transparent `2.00 μm` cylindrical rod with refractive index `1.36`,
there is a largest external angle whose ray is guided by total internal
reflection. Its exact geometrical-optics expression is the usual numerical
aperture formula, and its degree readout rounds to answer C, `67.2°`.

The diameter is retained as dimensionful figure data. It does not enter the
acceptance-angle formula in this geometrical-optics model.

Blueprint: `thm:physics:phyx_mini_0010:target`.
-/
theorem problem_phyx_mini_0010
    (setup : CylindricalRodSetup)
    (_figure : CylindricalRodFigureReadouts setup) :
    ∃ thetaMaxRadians : ℝ,
      IsMaximumGuidedAngle setup thetaMaxRadians ∧
        thetaMaxRadians =
          Real.arcsin
            (Real.sqrt
                (setup.refractiveIndex .transparentRod ^ 2 -
                  setup.refractiveIndex .exteriorAir ^ 2) /
              setup.refractiveIndex .incidentAir) ∧
        MatchesAnswerToNearestTenth thetaMaxRadians .C := by
  set_option maxHeartbeats 800000 in
    let s : ℝ := Real.sqrt ((531 : ℝ) / 625)
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      positivity
    have hs_sq : s ^ 2 = (531 : ℝ) / 625 := by
      dsimp [s]
      exact Real.sq_sqrt (by norm_num)
    have hs_le_one : s ≤ 1 := by
      nlinarith only [hs_nonneg, hs_sq]
    have hs_mem : s ∈ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨by linarith, hs_le_one⟩
    have hsin_arcsin : Real.sin (Real.arcsin s) = s :=
      Real.sin_arcsin hs_mem.1 hs_mem.2
    have harcsin_mem : Real.arcsin s ∈ Set.Icc 0 (Real.pi / 2) := by
      exact ⟨Real.arcsin_nonneg.2 hs_nonneg, Real.arcsin_le_pi_div_two s⟩

    have hround :
        MatchesAnswerToNearestTenth (Real.arcsin s) .C := by
      have hpi_bounds : (3 : ℝ) < Real.pi ∧ Real.pi < (33 : ℝ) / 10 := by
        have hsin_half : Real.sin ((1 : ℝ) / 2) < (1 : ℝ) / 2 := by
          have hbound := Real.sin_bound (x := (1 : ℝ) / 2) (by norm_num)
          rw [abs_le] at hbound
          norm_num at hbound ⊢
          linarith
        have hsin_eleven_twentieth :
            (1 : ℝ) / 2 < Real.sin ((11 : ℝ) / 20) := by
          have hbound :=
            Real.sin_bound (x := (11 : ℝ) / 20) (by norm_num)
          rw [abs_le] at hbound
          norm_num at hbound ⊢
          linarith
        have hpi_six_mem :
            Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.pi_pos]
        have hhalf_mem :
            (1 : ℝ) / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.one_le_pi_div_two]
        have heleven_twentieth_mem :
            (11 : ℝ) / 20 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.one_le_pi_div_two]
        have hsin_pi_six :
            Real.sin (Real.pi / 6) = (1 : ℝ) / 2 :=
          Real.sin_pi_div_six
        constructor
        · by_contra h
          have hangle : Real.pi / 6 ≤ (1 : ℝ) / 2 := by
            nlinarith only [le_of_not_gt h]
          have hsine :=
            Real.strictMonoOn_sin.monotoneOn hpi_six_mem hhalf_mem hangle
          linarith only [hsine, hsin_half, hsin_pi_six]
        · by_contra h
          have hangle : (11 : ℝ) / 20 ≤ Real.pi / 6 := by
            nlinarith only [le_of_not_gt h]
          have hsine :=
            Real.strictMonoOn_sin.monotoneOn
              heleven_twentieth_mem hpi_six_mem hangle
          linarith only [hsine, hsin_eleven_twentieth, hsin_pi_six]
      rcases hpi_bounds with ⟨hpi_lower, hpi_upper⟩

      have hs_bounds :
          (9217 : ℝ) / 10000 ≤ s ∧ s ≤ (9218 : ℝ) / 10000 := by
        constructor <;> nlinarith only [hs_nonneg, hs_sq]
      rcases hs_bounds with ⟨hs_lower, hs_upper⟩

      let c : ℝ := Real.sqrt (2 + Real.sqrt 2) / 2
      let q : ℝ := Real.sqrt (2 - Real.sqrt 2) / 2
      have hroot_bounds :
          (9238 : ℝ) / 10000 ≤ c ∧ c ≤ (9239 : ℝ) / 10000 ∧
            (3826 : ℝ) / 10000 ≤ q ∧ q ≤ (3827 : ℝ) / 10000 := by
        have hsqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        have hsqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
          Real.sq_sqrt (by norm_num)
        have hsqrt_two_lower : (14142 : ℝ) / 10000 ≤ Real.sqrt 2 := by
          nlinarith only [hsqrt_two_nonneg, hsqrt_two_sq]
        have hsqrt_two_upper : Real.sqrt 2 ≤ (14143 : ℝ) / 10000 := by
          nlinarith only [hsqrt_two_nonneg, hsqrt_two_sq]
        have hc_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by
          positivity
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          positivity
        have hc_sq : (2 * c) ^ 2 = (2 : ℝ) + Real.sqrt 2 := by
          dsimp [c]
          convert Real.sq_sqrt hc_arg using 1 <;> ring
        have hq_arg : 0 ≤ (2 : ℝ) - Real.sqrt 2 := by
          nlinarith only [hsqrt_two_nonneg, hsqrt_two_sq]
        have hq_nonneg : 0 ≤ q := by
          dsimp [q]
          positivity
        have hq_sq : (2 * q) ^ 2 = (2 : ℝ) - Real.sqrt 2 := by
          dsimp [q]
          convert Real.sq_sqrt hq_arg using 1 <;> ring
        constructor
        · nlinarith only [hsqrt_two_lower, hc_nonneg, hc_sq]
        constructor
        · nlinarith only [hsqrt_two_upper, hc_nonneg, hc_sq]
        constructor
        · nlinarith only [hsqrt_two_upper, hq_nonneg, hq_sq]
        · nlinarith only [hsqrt_two_lower, hq_nonneg, hq_sq]
      rcases hroot_bounds with ⟨hc_lower, hc_upper, hq_lower, hq_upper⟩
      have hc_nonneg : 0 ≤ c := by
        dsimp [c]
        positivity
      have hq_nonneg : 0 ≤ q := by
        dsimp [q]
        positivity
      have hsin_three_eighth : Real.sin (3 * Real.pi / 8) = c := by
        rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
          Real.sin_pi_div_two_sub, Real.cos_pi_div_eight]
      have hcos_three_eighth : Real.cos (3 * Real.pi / 8) = q := by
        rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
          Real.cos_pi_div_two_sub, Real.sin_pi_div_eight]

      have hlower_sine :
          Real.sin ((1343 : ℝ) * Real.pi / 3600) ≤ s := by
        let d : ℝ := 7 * Real.pi / 3600
        have hd_nonneg : 0 ≤ d := by
          dsimp [d]
          positivity
        have hd_lower : (7 : ℝ) / 1200 < d := by
          dsimp [d]
          nlinarith only [hpi_lower]
        have hd_upper : d < (13 : ℝ) / 2000 := by
          dsimp [d]
          nlinarith only [hpi_upper]
        have hd_abs : |d| ≤ 1 := by
          rw [abs_of_nonneg hd_nonneg]
          linarith
        have hsin_bound := Real.sin_bound hd_abs
        rw [abs_le, abs_of_nonneg hd_nonneg] at hsin_bound
        have hd_cube : d ^ 3 ≤ ((13 : ℝ) / 2000) ^ 3 :=
          pow_le_pow_left₀ hd_nonneg hd_upper.le 3
        have hd_fourth : d ^ 4 ≤ ((13 : ℝ) / 2000) ^ 4 :=
          pow_le_pow_left₀ hd_nonneg hd_upper.le 4
        have hsin_d_lower : (5833 : ℝ) / 1000000 ≤ Real.sin d := by
          nlinarith only [hd_lower, hd_cube, hd_fourth, hsin_bound.1]
        have hcos_product : c * Real.cos d ≤ (9239 : ℝ) / 10000 := by
          calc
            c * Real.cos d ≤ c * 1 :=
              mul_le_mul_of_nonneg_left (Real.cos_le_one d) hc_nonneg
            _ ≤ (9239 : ℝ) / 10000 := by linarith
        have hsin_product :
            (3826 : ℝ) / 10000 * ((5833 : ℝ) / 1000000) ≤
              q * Real.sin d := by
          exact mul_le_mul hq_lower hsin_d_lower (by norm_num) hq_nonneg
        rw [show (1343 : ℝ) * Real.pi / 3600 =
            3 * Real.pi / 8 - d by dsimp [d]; ring,
          Real.sin_sub, hsin_three_eighth, hcos_three_eighth]
        linarith only [hcos_product, hsin_product, hs_lower]

      have hupper_sine :
          s ≤ Real.sin ((269 : ℝ) * Real.pi / 720) := by
        let d : ℝ := Real.pi / 720
        have hd_nonneg : 0 ≤ d := by
          dsimp [d]
          positivity
        have hd_upper : d < (11 : ℝ) / 2400 := by
          dsimp [d]
          nlinarith only [hpi_upper]
        have hd_abs : |d| ≤ 1 := by
          rw [abs_of_nonneg hd_nonneg]
          linarith
        have hcos_bound := Real.cos_bound hd_abs
        have hsin_bound := Real.sin_bound hd_abs
        rw [abs_le, abs_of_nonneg hd_nonneg] at hcos_bound hsin_bound
        have hd_sq : d ^ 2 ≤ ((11 : ℝ) / 2400) ^ 2 :=
          pow_le_pow_left₀ hd_nonneg hd_upper.le 2
        have hd_cube : d ^ 3 ≤ ((11 : ℝ) / 2400) ^ 3 :=
          pow_le_pow_left₀ hd_nonneg hd_upper.le 3
        have hd_fourth : d ^ 4 ≤ ((11 : ℝ) / 2400) ^ 4 :=
          pow_le_pow_left₀ hd_nonneg hd_upper.le 4
        have hcos_d_lower : (999989 : ℝ) / 1000000 ≤ Real.cos d := by
          nlinarith only [hd_sq, hd_fourth, hcos_bound.1]
        have hd_cube_nonneg : 0 ≤ d ^ 3 := by
          positivity
        have hsin_d_upper : Real.sin d ≤ (4584 : ℝ) / 1000000 := by
          nlinarith only [hd_upper, hd_cube_nonneg, hd_fourth, hsin_bound.2]
        have hsin_d_nonneg : 0 ≤ Real.sin d :=
          Real.sin_nonneg_of_nonneg_of_le_pi hd_nonneg
            (by dsimp [d]; nlinarith only [Real.pi_pos])
        have hcos_product :
            (9238 : ℝ) / 10000 * ((999989 : ℝ) / 1000000) ≤
              c * Real.cos d := by
          exact mul_le_mul hc_lower hcos_d_lower (by norm_num) hc_nonneg
        have hsin_product :
            q * Real.sin d ≤
              (3827 : ℝ) / 10000 * ((4584 : ℝ) / 1000000) := by
          exact mul_le_mul hq_upper hsin_d_upper hsin_d_nonneg (by norm_num)
        rw [show (269 : ℝ) * Real.pi / 720 =
            3 * Real.pi / 8 - d by dsimp [d]; ring,
          Real.sin_sub, hsin_three_eighth, hcos_three_eighth]
        linarith only [hcos_product, hsin_product, hs_upper]

      have hlower_angle :
          (1343 : ℝ) * Real.pi / 3600 ≤ Real.arcsin s := by
        have hangle_mem :
            (1343 : ℝ) * Real.pi / 3600 ∈
              Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.pi_pos]
        exact (Real.le_arcsin_iff_sin_le hangle_mem hs_mem).2 hlower_sine
      have hupper_angle :
          Real.arcsin s ≤ (269 : ℝ) * Real.pi / 720 := by
        have hangle_mem :
            (269 : ℝ) * Real.pi / 720 ∈
              Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith only [Real.pi_pos]
        exact (Real.arcsin_le_iff_le_sin hs_mem hangle_mem).2 hupper_sine
      simp only [MatchesAnswerToNearestTenth, degreeReadout, answerAngleDegrees]
      rw [abs_le]
      constructor
      · have hcleared :
            (67.15 : ℝ) * Real.pi ≤ Real.arcsin s * 180 := by
          nlinarith only [hlower_angle]
        have := (le_div_iff₀ Real.pi_pos).2 hcleared
        nlinarith only [this]
      · have hcleared :
            Real.arcsin s * 180 ≤ (67.25 : ℝ) * Real.pi := by
          nlinarith only [hupper_angle]
        have := (div_le_iff₀ Real.pi_pos).2 hcleared
        nlinarith only [this]

    have hmaximum : IsMaximumGuidedAngle setup (Real.arcsin s) := by
      have hincident : setup.refractiveIndex .incidentAir = 1 :=
        _figure.incident_air_index
      have hrod : setup.refractiveIndex .transparentRod = 1.36 :=
        _figure.rod_index
      have hexterior : setup.refractiveIndex .exteriorAir = 1 :=
        _figure.exterior_air_index
      let insideLimit : ℝ := Real.arccos ((25 : ℝ) / 34)
      have hinside_mem : insideLimit ∈ Set.Icc 0 (Real.pi / 2) := by
        exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (by norm_num)⟩
      have hcos_inside : Real.cos insideLimit = (25 : ℝ) / 34 := by
        dsimp [insideLimit]
        exact Real.cos_arccos (by norm_num) (by norm_num)
      have hsin_inside_nonneg : 0 ≤ Real.sin insideLimit :=
        Real.sin_nonneg_of_nonneg_of_le_pi hinside_mem.1
          (by nlinarith [hinside_mem.2, Real.pi_pos])
      have hscaled_inside :
          (34 : ℝ) / 25 * Real.sin insideLimit = s := by
        nlinarith [Real.sin_sq_add_cos_sq insideLimit]
      constructor
      · constructor
        · exact harcsin_mem
        · refine ⟨insideLimit, hinside_mem, ?_, ?_⟩
          · simp only [SatisfiesEndFaceSnellLaw]
            rw [hincident, hrod, hsin_arcsin]
            norm_num
            nlinarith
          · simp only [MeetsWallTotalInternalReflectionThreshold,
              wallIncidenceAngleRadians]
            rw [hexterior, hrod, Real.sin_pi_div_two_sub, hcos_inside]
            norm_num
      · intro otherTheta hguided
        rcases hguided with
          ⟨hother_mem, insideAngle, hinside_angle_mem, hsnell, hwall⟩
        simp only [SatisfiesEndFaceSnellLaw] at hsnell
        rw [hincident, hrod] at hsnell
        norm_num at hsnell
        simp only [MeetsWallTotalInternalReflectionThreshold,
            wallIncidenceAngleRadians] at hwall
        rw [hexterior, hrod, Real.sin_pi_div_two_sub] at hwall
        norm_num at hwall
        have hsin_inside_nonneg' : 0 ≤ Real.sin insideAngle :=
          Real.sin_nonneg_of_nonneg_of_le_pi hinside_angle_mem.1
            (by nlinarith [hinside_angle_mem.2, Real.pi_pos])
        have hcos_inside_nonneg : 0 ≤ Real.cos insideAngle :=
          Real.cos_nonneg_of_mem_Icc
            ⟨by nlinarith [hinside_angle_mem.1, Real.pi_pos],
              hinside_angle_mem.2⟩
        have hcos_inside_lower : (25 : ℝ) / 34 ≤ Real.cos insideAngle := by
          nlinarith
        have hcos_sq_lower :
            ((25 : ℝ) / 34) ^ 2 ≤ Real.cos insideAngle ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hcos_inside_lower 2
        have hscaled_inside_upper :
            (34 : ℝ) / 25 * Real.sin insideAngle ≤ s := by
          nlinarith [Real.sin_sq_add_cos_sq insideAngle]
        have hsine_other :
            Real.sin otherTheta ≤ Real.sin (Real.arcsin s) := by
          rw [hsin_arcsin]
          nlinarith
        apply
          (Real.strictMonoOn_sin.le_iff_le
            ⟨by nlinarith [hother_mem.1, Real.pi_pos], hother_mem.2⟩
            ⟨by nlinarith [harcsin_mem.1, Real.pi_pos], harcsin_mem.2⟩).1
        exact hsine_other

    refine ⟨Real.arcsin s, hmaximum, ?_, hround⟩
    rw [_figure.rod_index, _figure.exterior_air_index,
      _figure.incident_air_index]
    norm_num [s]

end PhyXMiniProblems.ProblemPhyXMini0010
