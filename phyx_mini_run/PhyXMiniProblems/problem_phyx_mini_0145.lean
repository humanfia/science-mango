import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Viewing the far bottom edge of a swimming pool

This file models the air--water refraction diagram for `phyx_mini_0145`.
Pool width and depth are dimensionful lengths. Refractive indices and radian
angle readouts are dimensionless. The `13.0°` label is the air-side elevation
above the horizontal surface, whereas Snell's law uses angles from the vertical
surface normal.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0145

open Dimension

/-- A physical length represented independently of a particular unit choice. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical readout of a dimensionful length in SI meters. -/
def lengthInMeters (quantity : DimLength) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Convert a degree readout to the scalar radian convention used below. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The homogeneous optical media on the two sides of the pool surface. -/
inductive OpticalMedium where
  | air
  | water
  deriving DecidableEq, Repr

/--
The physical quantities and angle labels in the pool-viewing diagram.

The air-side angle is measured above the horizontal interface. The incidence
and refraction angles are measured from the vertical interface normal, as
required by Snell's law. No numerical value for the requested depth is stored
in this setup.
-/
structure PoolViewingSetup where
  /-- Figure label `x`: horizontal width of the water-filled pool. -/
  poolWidth : DimLength
  /-- Figure label `Depth ?`: vertical distance from surface to far bottom. -/
  poolDepth : DimLength
  /-- Dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Figure label `13.0°`, measured above the horizontal on the air side. -/
  airRayElevationRadians : ℝ
  /-- Incidence angle in air, measured from the vertical surface normal. -/
  airIncidenceAngleRadians : ℝ
  /-- Refracted-ray angle in water, measured from the vertical normal. -/
  waterRefractionAngleRadians : ℝ

/-- The measured labels and complementary-angle relation read from the figure. -/
structure MatchesPoolFigure (setup : PoolViewingSetup) : Prop where
  /-- The horizontal underwater run to the far wall is `6.50 m`. -/
  widthReadout : lengthInMeters setup.poolWidth = 6.50
  /-- The observer's line of sight is `13.0°` above the horizontal. -/
  airElevationReadout :
    setup.airRayElevationRadians = degreesToRadians 13.0
  /-- Horizontal surface and vertical normal make the labelled angles complementary. -/
  airAnglesComplementary :
    setup.airIncidenceAngleRadians + setup.airRayElevationRadians =
      Real.pi / 2

/-- Standard dimensionless refractive-index readouts used for air and water. -/
structure HasStandardAirWaterIndices (setup : PoolViewingSetup) : Prop where
  airIndexReadout : setup.refractiveIndex .air = 1.00
  waterIndexReadout : setup.refractiveIndex .water = 1.33

/-- An angle readout lies on the strictly acute geometrical-optics branch. -/
def IsAcuteRadians (angleRadians : ℝ) : Prop :=
  0 < angleRadians ∧ angleRadians < Real.pi / 2

/-- Positivity and principal-branch conditions for the depicted physical setup. -/
structure HasPhysicalPoolViewingParameters (setup : PoolViewingSetup) : Prop where
  poolWidthPositive : 0 < lengthInMeters setup.poolWidth
  poolDepthPositive : 0 < lengthInMeters setup.poolDepth
  refractiveIndicesPositive :
    ∀ medium, 0 < setup.refractiveIndex medium
  airElevationAcute : IsAcuteRadians setup.airRayElevationRadians
  airIncidenceAcute : IsAcuteRadians setup.airIncidenceAngleRadians
  waterRefractionAcute : IsAcuteRadians setup.waterRefractionAngleRadians

/--
Snell's law for transmission from air into water at the flat pool surface,
with both angles measured from the surface normal.
-/
structure SatisfiesAirWaterSnellLaw (setup : PoolViewingSetup) : Prop where
  snellLaw :
    setup.refractiveIndex .air *
        Real.sin setup.airIncidenceAngleRadians =
      setup.refractiveIndex .water *
        Real.sin setup.waterRefractionAngleRadians

/--
Right-triangle geometry for the underwater ray from the near surface point to
the far bottom edge: `tan θ_water = width / depth`, where `θ_water` is measured
from the vertical normal.
-/
structure SatisfiesFarBottomRayGeometry (setup : PoolViewingSetup) : Prop where
  farBottomEdgeRelation :
    lengthInMeters setup.poolWidth =
      lengthInMeters setup.poolDepth *
        Real.tan setup.waterRefractionAngleRadians

/-- The four pool-depth choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter readout printed beside each answer choice. -/
def answerDepthMeters : AnswerChoice → ℝ
  | .A => 6.12
  | .B => 6.08
  | .C => 6.04
  | .D => 6.00

/-- Agreement with an answer displayed to the nearest hundredth of a meter. -/
def MatchesAnswerToNearestHundredth
    (depth : DimLength) (choice : AnswerChoice) : Prop :=
  |lengthInMeters depth - answerDepthMeters choice| ≤ 0.005

/--
The far-bottom ray geometry expresses the depth as the width divided by the
tangent of the underwater angle. This is a derived relation, not figure data.
-/
lemma pool_depth_from_far_bottom_geometry
    (setup : PoolViewingSetup)
    (geometry : SatisfiesFarBottomRayGeometry setup)
    (h_tan_ne_zero : Real.tan setup.waterRefractionAngleRadians ≠ 0) :
    lengthInMeters setup.poolDepth =
      lengthInMeters setup.poolWidth /
        Real.tan setup.waterRefractionAngleRadians := by
  exact (eq_div_iff h_tan_ne_zero).2 geometry.farBottomEdgeRelation.symm

/--
For a `6.50 m`-wide pool viewed at `13.0°` above horizontal, standard air and
water refractive indices, Snell's law, and the far-bottom ray geometry make the
pool depth round to `6.04 m`, answer C.

Blueprint: `thm:physics:phyx_mini_0145:target`.
-/
theorem problem_phyx_mini_0145
    (setup : PoolViewingSetup)
    (figure : MatchesPoolFigure setup)
    (indices : HasStandardAirWaterIndices setup)
    (physical : HasPhysicalPoolViewingParameters setup)
    (refraction : SatisfiesAirWaterSnellLaw setup)
    (geometry : SatisfiesFarBottomRayGeometry setup) :
    MatchesAnswerToNearestHundredth setup.poolDepth .C := by
  let d : ℝ := lengthInMeters setup.poolDepth
  let q : ℝ := Real.cos (13 * Real.pi / 180)
  let s : ℝ := Real.sin setup.waterRefractionAngleRadians
  let c : ℝ := Real.cos setup.waterRefractionAngleRadians
  have hd_pos : 0 < d := by simpa [d] using physical.poolDepthPositive
  have hw_pos : 0 < setup.waterRefractionAngleRadians :=
    physical.waterRefractionAcute.1
  have hw_lt : setup.waterRefractionAngleRadians < Real.pi / 2 :=
    physical.waterRefractionAcute.2
  have hc_pos : 0 < c := by
    dsimp [c]
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by nlinarith only [Real.pi_pos, hw_pos], hw_lt⟩
  have hc_ne : Real.cos setup.waterRefractionAngleRadians ≠ 0 := by
    simpa [c] using hc_pos.ne'
  have h_elevation := figure.airElevationReadout
  norm_num [degreesToRadians] at h_elevation
  have h_air_angle : setup.airIncidenceAngleRadians =
      Real.pi / 2 - 13 * Real.pi / 180 := by
    linarith only [figure.airAnglesComplementary, h_elevation]
  have h_air_sin : Real.sin setup.airIncidenceAngleRadians = q := by
    rw [h_air_angle, Real.sin_pi_div_two_sub]
  have hsnell : q = (1.33 : ℝ) * s := by
    have h := refraction.snellLaw
    rw [indices.airIndexReadout, indices.waterIndexReadout, h_air_sin] at h
    norm_num at h ⊢
    simpa [s] using h
  have hgeom : (6.5 : ℝ) * c = d * s := by
    have h := geometry.farBottomEdgeRelation
    rw [figure.widthReadout, Real.tan_eq_sin_div_cos] at h
    field_simp [hc_ne] at h
    norm_num at h ⊢
    simpa [d, s, c] using h
  have htrig : s ^ 2 + c ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq setup.waterRefractionAngleRadians

  -- First obtain the two-decimal bounds on π needed by the Taylor estimate below.
  have ha_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have ha_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [ha_nonneg, ha_sq]
  have ha_upper : Real.sqrt 2 < (1.41422 : ℝ) := by
    nlinarith only [ha_nonneg, ha_sq]
  have hb_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hb_sq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hb_lower : (1.8471 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hb_nonneg, hb_sq, ha_lower]
  have hb_upper : Real.sqrt (2 + Real.sqrt 2) < (1.84777 : ℝ) := by
    nlinarith only [hb_nonneg, hb_sq, ha_upper]
  have hs_pos : 0 < Real.sin (Real.pi / 16) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith only [Real.pi_pos]
  have hs_sq : Real.sin (Real.pi / 16) ^ 2 =
      (2 - Real.sqrt (2 + Real.sqrt 2)) / 4 := by
    have h := Real.sin_sq_pi_over_two_pow_succ 2
    norm_num [Real.sqrtTwoAddSeries] at h ⊢
    nlinarith only [h]
  have hs_lower : (0.19508 : ℝ) < Real.sin (Real.pi / 16) := by
    nlinarith only [hs_pos, hs_sq, hb_upper,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19508)]
  have hs_upper : Real.sin (Real.pi / 16) < (0.19552 : ℝ) := by
    nlinarith only [hs_pos, hs_sq, hb_lower,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19552)]
  have hsin_314_upper : Real.sin (3.14 / 16) < (0.19508 : ℝ) := by
    have h := Real.sin_bound (x := (3.14 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.14 / 16)] at h
    rcases abs_le.mp h with ⟨_, hupper⟩
    norm_num at hupper ⊢
    linarith only [hupper]
  have hsin_315_lower : (0.19552 : ℝ) < Real.sin (3.15 / 16) := by
    have h := Real.sin_bound (x := (3.15 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.15 / 16)] at h
    rcases abs_le.mp h with ⟨hlower, _⟩
    norm_num at hlower ⊢
    linarith only [hlower]
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    by_contra hpi
    have hpi_le : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt hpi
    have hsin_mono :
        Real.sin (Real.pi / 16) ≤ Real.sin (3.14 / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.one_le_pi_div_two]
      · nlinarith only [hpi_le]
    linarith only [hs_lower, hsin_mono, hsin_314_upper]
  have hpi_upper : Real.pi < (3.15 : ℝ) := by
    by_contra hpi
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hsin_mono :
        Real.sin (3.15 / 16) ≤ Real.sin (Real.pi / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · nlinarith only [hpi_ge]
    linarith only [hsin_315_lower, hsin_mono, hs_upper]

  -- A fourth-order Taylor remainder now bounds cos(13°) tightly enough.
  let x : ℝ := 13 * Real.pi / 180
  let xl : ℝ := 13 * 3.14 / 180
  let xu : ℝ := 13 * 3.15 / 180
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxl_nonneg : 0 ≤ xl := by norm_num [xl]
  have hxl_le : xl ≤ x := by
    dsimp [xl, x]
    nlinarith only [hpi_lower]
  have hx_le : x ≤ xu := by
    dsimp [x, xu]
    nlinarith only [hpi_upper]
  have hxu_le_one : xu ≤ 1 := by norm_num [xu]
  have hx_abs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    exact hx_le.trans hxu_le_one
  have hxl_sq_le : xl ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ hxl_nonneg hxl_le 2
  have hx_sq_le : x ^ 2 ≤ xu ^ 2 :=
    pow_le_pow_left₀ hx_nonneg hx_le 2
  have hx_four_le : x ^ 4 ≤ xu ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le 4
  have hcos_bound := Real.cos_bound hx_abs
  rw [abs_of_nonneg hx_nonneg] at hcos_bound
  rcases abs_le.mp hcos_bound with ⟨hcos_lower, hcos_upper⟩
  dsimp [xl, xu] at hxl_sq_le hx_sq_le hx_four_le
  have hq_lower : (0.97395 : ℝ) < q := by
    dsimp [q]
    change (0.97395 : ℝ) < Real.cos x
    nlinarith only [hcos_lower, hx_sq_le, hx_four_le]
  have hq_upper : q < (0.9746 : ℝ) := by
    dsimp [q]
    change Real.cos x < (0.9746 : ℝ)
    nlinarith only [hcos_upper, hxl_sq_le, hx_four_le]

  -- Eliminate the underwater angle from Snell's law and the ray triangle.
  have hsnell_mul := congrArg (fun z : ℝ => d * z) hsnell
  have hdq : d * q = (6.5 : ℝ) * 1.33 * c := by
    calc
      d * q = d * (1.33 * s) := hsnell_mul
      _ = 1.33 * (d * s) := by ring
      _ = 1.33 * (6.5 * c) := by rw [← hgeom]
      _ = 6.5 * 1.33 * c := by ring
  have hsnell_sq := congrArg (fun z : ℝ => z ^ 2) hsnell
  have hdq_sq := congrArg (fun z : ℝ => z ^ 2) hdq
  have hscaled_trig : (1.33 : ℝ) ^ 2 * c ^ 2 =
      (1.33 : ℝ) ^ 2 - q ^ 2 := by
    nlinarith only [hsnell_sq, htrig]
  have hdepth_sq : d ^ 2 * q ^ 2 =
      (6.5 : ℝ) ^ 2 * ((1.33 : ℝ) ^ 2 - q ^ 2) := by
    ring_nf at hdq_sq ⊢
    nlinarith only [hdq_sq, hscaled_trig]
  have hproduct : (6.5 : ℝ) ^ 2 * (1.33 : ℝ) ^ 2 =
      q ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) := by
    nlinarith only [hdepth_sq]
  have hq_pos : 0 < q := by nlinarith only [hq_lower]

  -- Compare the exact squared relation with the two rounding endpoints.
  have hd_lower : (6.035 : ℝ) ≤ d := by
    by_contra hnot
    have hd_lt : d < (6.035 : ℝ) := lt_of_not_ge hnot
    have hd_sq_lt : d ^ 2 < (6.035 : ℝ) ^ 2 := by
      nlinarith only [hd_pos, hd_lt]
    have hq_sq_lt : q ^ 2 < (0.9746 : ℝ) ^ 2 := by
      nlinarith only [hq_pos, hq_upper]
    have hprod_lt : q ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) <
        (0.9746 : ℝ) ^ 2 *
          ((6.035 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) := by
      calc
        q ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) <
            (0.9746 : ℝ) ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_right hq_sq_lt (by positivity)
        _ < (0.9746 : ℝ) ^ 2 *
              ((6.035 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left (by nlinarith only [hd_sq_lt]) (by norm_num)
    have hnumeric : (0.9746 : ℝ) ^ 2 *
          ((6.035 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) <
        (6.5 : ℝ) ^ 2 * (1.33 : ℝ) ^ 2 := by
      norm_num
    nlinarith only [hproduct, hprod_lt, hnumeric]
  have hd_upper : d ≤ (6.045 : ℝ) := by
    by_contra hnot
    have hd_gt : (6.045 : ℝ) < d := lt_of_not_ge hnot
    have hd_sq_gt : (6.045 : ℝ) ^ 2 < d ^ 2 := by
      nlinarith only [hd_pos, hd_gt]
    have hq_sq_gt : (0.97395 : ℝ) ^ 2 < q ^ 2 := by
      nlinarith only [hq_pos, hq_lower]
    have hprod_gt : (0.97395 : ℝ) ^ 2 *
          ((6.045 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) <
        q ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) := by
      calc
        (0.97395 : ℝ) ^ 2 *
              ((6.045 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) <
            q ^ 2 * ((6.045 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_right hq_sq_gt (by positivity)
        _ < q ^ 2 * (d ^ 2 + (6.5 : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left (by nlinarith only [hd_sq_gt]) (by positivity)
    have hnumeric : (6.5 : ℝ) ^ 2 * (1.33 : ℝ) ^ 2 <
        (0.97395 : ℝ) ^ 2 *
          ((6.045 : ℝ) ^ 2 + (6.5 : ℝ) ^ 2) := by
      norm_num
    nlinarith only [hproduct, hprod_gt, hnumeric]
  rw [MatchesAnswerToNearestHundredth, answerDepthMeters, abs_le]
  change -(0.005 : ℝ) ≤ d - 6.04 ∧ d - 6.04 ≤ 0.005
  constructor <;> nlinarith only [hd_lower, hd_upper]

end PhyXMiniProblems.ProblemPhyXMini0145
