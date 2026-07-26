import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Units.WithDim.Basic

/-!
# Reflected light between two perpendicular mirrors

The coordinates below are SI-metre readouts in the three-dimensional Euclidean space of the
figure.  Physical lengths themselves use Physlib's dimension-carrying quantity type.
-/

namespace PhyXMiniProblems.Problem0002

open Dimension CarriesDimension UnitChoices

/-- The Euclidean space containing both mirrors and the light rays.  Coordinates are read in
metres when they are converted to physical lengths. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A physical quantity with the dimension of length. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- Turn an SI-metre readout into a dimensionful physical length. -/
noncomputable def metres (value : ℝ) : LengthQuantity :=
  toDimensionful SI ⟨value⟩

/-- The SI-metre readout of a physical length. -/
noncomputable def siMetres (length : LengthQuantity) : ℝ :=
  (length SI).val

/-- The physical distance between two points whose coordinates are SI-metre readouts. -/
noncomputable def physicalDistance (p q : Space) : LengthQuantity :=
  metres (dist p q)

/-- Convert the angle read from the figure in degrees to the radians used by Mathlib. -/
noncomputable def degrees (value : ℝ) : ℝ :=
  value * Real.pi / 180

/-- An oriented light ray with a unit direction vector.  Its nonnegative parameter in
`pointAt` is therefore the travelled distance in metres. -/
structure LightRay where
  origin : Space
  direction : Space
  direction_ne_zero : direction ≠ 0
  direction_is_unit : ‖direction‖ = 1

namespace LightRay

/-- The point reached after the given signed SI-metre parameter along a light ray. -/
def pointAt (ray : LightRay) (distanceMetres : ℝ) : Space :=
  distanceMetres • ray.direction + ray.origin

end LightRay

/-- An ideal plane mirror.  The final field says that `unitNormal` really characterizes the
codimension-one direction of the reflecting surface. -/
structure PlaneMirror where
  surface : AffineSubspace ℝ Space
  surface_nonempty : Nonempty surface
  unitNormal : Space
  normal_is_unit : ‖unitNormal‖ = 1
  mem_direction_iff_inner_normal_zero :
    ∀ v : Space, v ∈ surface.direction ↔ @inner ℝ Space _ v unitNormal = 0

namespace PlaneMirror

/-- Reflect a propagation direction in the affine plane of a mirror.  Translating the direction
to a point of incidence and back lets us directly use Mathlib's affine reflection. -/
noncomputable def reflectDirection (mirror : PlaneMirror) (impact direction : Space) : Space :=
  letI : Nonempty mirror.surface := mirror.surface_nonempty
  EuclideanGeometry.reflection mirror.surface (direction + impact) - impact

end PlaneMirror

/-- The incident ray reaches the indicated point on the indicated mirror. -/
def IsIncidentAt (ray : LightRay) (mirror : PlaneMirror) (impact : Space) : Prop :=
  impact ∈ mirror.surface ∧
    ∃ distanceMetres : ℝ, 0 ≤ distanceMetres ∧ ray.pointAt distanceMetres = impact

/-- The ray strikes the indicated mirror at a strictly positive distance from its origin. -/
def StrikesAt (ray : LightRay) (mirror : PlaneMirror) (strike : Space) : Prop :=
  strike ∈ mirror.surface ∧
    ∃ distanceMetres : ℝ, 0 < distanceMetres ∧ ray.pointAt distanceMetres = strike

/-- The governing law of specular reflection at Mirror 1. -/
def IsSpecularReflectionAt
    (incoming reflected : LightRay) (mirror : PlaneMirror) (impact : Space) : Prop :=
  IsIncidentAt incoming mirror impact ∧
    reflected.origin = impact ∧
    reflected.direction = mirror.reflectDirection impact incoming.direction

/-- The two plane mirrors share the marked corner and have orthogonal unit normals. -/
def MeetAtRightAngle
    (mirror1 mirror2 : PlaneMirror) (corner : Space) : Prop :=
  corner ∈ mirror1.surface ∧
    corner ∈ mirror2.surface ∧
    @inner ℝ Space _ mirror1.unitNormal mirror2.unitNormal = 0

/-- All physical objects and figure readouts for the dashed vertical cross-section.  In
particular, no field gives the requested reflected travel distance. -/
structure Configuration where
  mirror1 : PlaneMirror
  mirror2 : PlaneMirror
  incoming : LightRay
  reflected : LightRay
  corner : Space
  impact : Space
  strike : Space
  verticalSection : AffineSubspace ℝ Space
  vertical_section_dimension : Module.finrank ℝ verticalSection.direction = 2
  mirrors_meet_at_right_angle : MeetAtRightAngle mirror1 mirror2 corner
  obeys_reflection_law : IsSpecularReflectionAt incoming reflected mirror1 impact
  reflected_strikes_mirror2 : StrikesAt reflected mirror2 strike
  corner_in_vertical_section : corner ∈ verticalSection
  incoming_origin_in_vertical_section : incoming.origin ∈ verticalSection
  impact_in_vertical_section : impact ∈ verticalSection
  strike_in_vertical_section : strike ∈ verticalSection
  mirror1_normal_in_vertical_section : mirror1.unitNormal ∈ verticalSection.direction
  mirror2_normal_in_vertical_section : mirror2.unitNormal ∈ verticalSection.direction
  cross_section_is_right_at_corner :
    EuclideanGeometry.angle impact corner strike = Real.pi / 2
  corner_to_impact_distance_readout :
    physicalDistance corner impact = metres (5 / 4 : ℝ)
  incidence_angle_readout :
    EuclideanGeometry.angle incoming.origin impact (mirror1.unitNormal + impact) =
      degrees 40

/-- Labels of the four multiple-choice answers shown with the problem. -/
inductive AnswerChoice
  | A | B | C | D
  deriving DecidableEq

/-- The SI-metre readout printed next to each answer choice. -/
noncomputable def answerMetres : AnswerChoice → ℝ
  | .A => 130 / 100
  | .B => 334 / 100
  | .C => 194 / 100
  | .D => 208 / 100

/-- The reflected light travels exactly `1.25 / sin(40°)` metres before it reaches Mirror 2,
and that value is within half a centimetre of the printed answer `C`, namely `1.94 m`. -/
theorem reflected_light_distance_is_choice_C (config : Configuration) :
    physicalDistance config.impact config.strike =
        metres ((5 / 4 : ℝ) / Real.sin (degrees 40)) ∧
      |siMetres (physicalDistance config.impact config.strike) - answerMetres .C| <
        (1 / 200 : ℝ) := by
  have numerical_bound :
      |(5 / 4 : ℝ) / Real.sin (degrees 40) - 194 / 100| < (200 : ℝ)⁻¹ := by
    let x : ℝ := degrees 40
    let s : ℝ := Real.sin x
    have htriple : Real.sin (3 * x) = 3 * s - 4 * s ^ 3 := by
      dsimp [s]
      rw [show 3 * x = 2 * x + x by ring, Real.sin_add, Real.sin_two_mul,
        Real.cos_two_mul]
      calc
        2 * Real.sin x * Real.cos x * Real.cos x +
            (2 * Real.cos x ^ 2 - 1) * Real.sin x =
          (3 * Real.sin x - 4 * Real.sin x ^ 3) +
            4 * Real.sin x * (Real.sin x ^ 2 + Real.cos x ^ 2 - 1) := by ring
        _ = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
          rw [Real.sin_sq_add_cos_sq]
          ring
    have hx : 3 * x = 2 * Real.pi / 3 := by
      dsimp [x, degrees]
      ring
    have hcubic : 3 * s - 4 * s ^ 3 = Real.sqrt 3 / 2 := by
      rw [hx, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.sin_pi_sub, Real.sin_pi_div_three] at htriple
      exact htriple.symm
    have hs_half : (1 / 2 : ℝ) < s := by
      rw [← Real.sin_pi_div_six]
      dsimp [s, x, degrees]
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
    have hs_nonneg : (0 : ℝ) ≤ s := by linarith only [hs_half]
    have hs_sq : (1 / 4 : ℝ) < s ^ 2 := by
      nlinarith only [hs_half, sq_nonneg (s - 1 / 2)]
    have hpoly_lower :
        Real.sqrt 3 / 2 <
          3 * (250 / 389 : ℝ) - 4 * (250 / 389 : ℝ) ^ 3 := by
      have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
      have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      have hp_pos :
          0 < 2 * (3 * (250 / 389 : ℝ) - 4 * (250 / 389 : ℝ) ^ 3) := by
        norm_num
      have hp_sq :
          3 < (2 * (3 * (250 / 389 : ℝ) - 4 * (250 / 389 : ℝ) ^ 3)) ^ 2 := by
        norm_num
      nlinarith only [hsqrt_sq, hsqrt_nonneg, hp_pos, hp_sq]
    have hpoly_upper :
        3 * (250 / 387 : ℝ) - 4 * (250 / 387 : ℝ) ^ 3 <
          Real.sqrt 3 / 2 := by
      have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
      have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      have hp_pos :
          0 < 2 * (3 * (250 / 387 : ℝ) - 4 * (250 / 387 : ℝ) ^ 3) := by
        norm_num
      have hp_sq :
          (2 * (3 * (250 / 387 : ℝ) - 4 * (250 / 387 : ℝ) ^ 3)) ^ 2 < 3 := by
        norm_num
      nlinarith only [hsqrt_sq, hsqrt_nonneg, hp_pos, hp_sq]
    have hs_lower : (250 / 389 : ℝ) < s := by
      by_contra h
      have hs_le : s ≤ (250 / 389 : ℝ) := le_of_not_gt h
      have hsr : (1 / 4 : ℝ) < s * (250 / 389 : ℝ) := by
        have hm := mul_lt_mul_of_pos_right hs_half
          (by norm_num : (0 : ℝ) < 250 / 389)
        norm_num at hm ⊢
        linarith only [hm]
      have hfactor :
          0 < 4 * (s ^ 2 + s * (250 / 389 : ℝ) + (250 / 389 : ℝ) ^ 2) - 3 := by
        norm_num at hsr ⊢
        nlinarith only [hs_sq, hsr]
      have hprod :
          0 ≤ ((250 / 389 : ℝ) - s) *
            (4 * (s ^ 2 + s * (250 / 389 : ℝ) + (250 / 389 : ℝ) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.mpr hs_le) hfactor.le
      have hmono :
          3 * (250 / 389 : ℝ) - 4 * (250 / 389 : ℝ) ^ 3 ≤
            3 * s - 4 * s ^ 3 := by
        nlinarith only [hprod]
      linarith only [hcubic, hpoly_lower, hmono]
    have hs_upper : s < (250 / 387 : ℝ) := by
      by_contra h
      have hr_le : (250 / 387 : ℝ) ≤ s := le_of_not_gt h
      have hsr : (1 / 4 : ℝ) < s * (250 / 387 : ℝ) := by
        have hm := mul_lt_mul_of_pos_right hs_half
          (by norm_num : (0 : ℝ) < 250 / 387)
        norm_num at hm ⊢
        linarith only [hm]
      have hfactor :
          0 < 4 * (s ^ 2 + s * (250 / 387 : ℝ) + (250 / 387 : ℝ) ^ 2) - 3 := by
        norm_num at hsr ⊢
        nlinarith only [hs_sq, hsr]
      have hprod :
          0 ≤ (s - (250 / 387 : ℝ)) *
            (4 * (s ^ 2 + s * (250 / 387 : ℝ) + (250 / 387 : ℝ) ^ 2) - 3) :=
        mul_nonneg (sub_nonneg.mpr hr_le) hfactor.le
      have hmono :
          3 * s - 4 * s ^ 3 ≤
            3 * (250 / 387 : ℝ) - 4 * (250 / 387 : ℝ) ^ 3 := by
        nlinarith only [hprod]
      linarith only [hcubic, hpoly_upper, hmono]
    have hs_pos : 0 < s := by linarith only [hs_half]
    have hdistance_lower : (387 / 200 : ℝ) < (5 / 4 : ℝ) / s := by
      rw [lt_div_iff₀ hs_pos]
      have hm := mul_lt_mul_of_pos_left hs_upper
        (by norm_num : (0 : ℝ) < 387 / 200)
      norm_num at hm ⊢
      exact hm
    have hdistance_upper : (5 / 4 : ℝ) / s < (389 / 200 : ℝ) := by
      rw [div_lt_iff₀ hs_pos]
      have hm := mul_lt_mul_of_pos_left hs_lower
        (by norm_num : (0 : ℝ) < 389 / 200)
      norm_num at hm ⊢
      exact hm
    rw [abs_lt]
    constructor
    · dsimp [s, x] at hdistance_lower
      norm_num at hdistance_lower ⊢
      linarith only [hdistance_lower]
    · dsimp [s, x] at hdistance_upper
      norm_num at hdistance_upper ⊢
      linarith only [hdistance_upper]
  let θ : ℝ := degrees 40
  let n₁ : Space := config.mirror1.unitNormal
  let n₂ : Space := config.mirror2.unitNormal
  let a : Space := config.impact - config.corner
  let b : Space := config.strike - config.corner
  let w : Space := config.strike - config.impact
  rcases config.mirrors_meet_at_right_angle with
    ⟨hcorner₁, hcorner₂, hn₁n₂⟩
  rcases config.obeys_reflection_law with
    ⟨⟨himpact₁, d, hd, hd_impact⟩, hreflected_origin, hreflected_direction⟩
  rcases config.reflected_strikes_mirror2 with
    ⟨hstrike₂, t, ht, ht_strike⟩
  have ha_mem₁ : a ∈ config.mirror1.surface.direction := by
    simpa [a, vsub_eq_sub] using
      config.mirror1.surface.vsub_mem_direction himpact₁ hcorner₁
  have hb_mem₂ : b ∈ config.mirror2.surface.direction := by
    simpa [b, vsub_eq_sub] using
      config.mirror2.surface.vsub_mem_direction hstrike₂ hcorner₂
  have ha_inner_n₁ : @inner ℝ Space _ a n₁ = 0 := by
    exact (config.mirror1.mem_direction_iff_inner_normal_zero a).1 ha_mem₁
  have hb_inner_n₂ : @inner ℝ Space _ b n₂ = 0 := by
    exact (config.mirror2.mem_direction_iff_inner_normal_zero b).1 hb_mem₂
  have hw : w = t • config.reflected.direction := by
    dsimp [LightRay.pointAt] at ht_strike
    rw [hreflected_origin] at ht_strike
    dsimp [w]
    exact (sub_eq_iff_eq_add).2 ht_strike.symm
  have hw_norm : ‖w‖ = t := by
    rw [hw, norm_smul, config.reflected.direction_is_unit, mul_one, Real.norm_eq_abs,
      abs_of_pos ht]
  have ha_norm : ‖a‖ = 5 / 4 := by
    have hreadout := config.corner_to_impact_distance_readout
    apply_fun fun q : LengthQuantity => siMetres q at hreadout
    have hdist_readout : dist config.corner config.impact = 5 / 4 := by
      simpa [physicalDistance, metres, siMetres,
        CarriesDimension.toDimensionful_apply_apply] using hreadout
    calc
      ‖a‖ = dist config.impact config.corner := by simp [a, dist_eq_norm]
      _ = dist config.corner config.impact := dist_comm _ _
      _ = 5 / 4 := hdist_readout
  have hb_parallel_n₁ :
      b = (@inner ℝ Space _ n₁ b) • n₁ := by
    let V : Submodule ℝ Space := config.verticalSection.direction
    have hn₁_mem_V : n₁ ∈ V := config.mirror1_normal_in_vertical_section
    have hn₂_mem_V : n₂ ∈ V := config.mirror2_normal_in_vertical_section
    have hb_mem_V : b ∈ V := by
      simpa [b, V, vsub_eq_sub] using
        config.verticalSection.vsub_mem_direction
          config.strike_in_vertical_section config.corner_in_vertical_section
    let e₁ : V := ⟨n₁, hn₁_mem_V⟩
    let e₂ : V := ⟨n₂, hn₂_mem_V⟩
    let bv : V := ⟨b, hb_mem_V⟩
    let e : Fin 2 → V := ![e₁, e₂]
    have he : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j
      · simp [e, e₁, n₁, config.mirror1.normal_is_unit]
      · simpa [e, e₁, e₂, n₁, n₂] using hn₁n₂
      · simpa [e, e₁, e₂, n₁, n₂, real_inner_comm] using hn₁n₂
      · simp [e, e₂, n₂, config.mirror2.normal_is_unit]
    have hcard : Fintype.card (Fin 2) = Module.finrank ℝ V := by
      simpa [V] using config.vertical_section_dimension.symm
    have hspan : (⊤ : Submodule ℝ V) ≤ Submodule.span ℝ (Set.range e) := by
      rw [he.linearIndependent.span_eq_top_of_card_eq_finrank hcard]
    let B : OrthonormalBasis (Fin 2) ℝ V := OrthonormalBasis.mk he hspan
    have hb_inner_n₂' : @inner ℝ Space _ n₂ b = 0 := by
      simpa [real_inner_comm] using hb_inner_n₂
    have hbv : bv = (@inner ℝ V _ e₁ bv) • e₁ := by
      have hsum := B.sum_repr' bv
      simpa [B, e, e₁, e₂, bv, hb_inner_n₂'] using hsum.symm
    simpa [bv, e₁] using congrArg Subtype.val hbv
  have ht_cos :
      @inner ℝ Space _ config.reflected.direction n₁ = Real.cos θ := by
    have hd_pos : 0 < d := by
      rcases hd.eq_or_lt with hd_zero | hd_pos
      · have horigin_impact : config.incoming.origin = config.impact := by
          rw [← hd_zero] at hd_impact
          simpa [LightRay.pointAt] using hd_impact
        have hangle := config.incidence_angle_readout
        rw [horigin_impact] at hangle
        simp only [EuclideanGeometry.angle_self_left] at hangle
        dsimp [degrees] at hangle
        nlinarith [Real.pi_pos]
      · exact hd_pos
    have hdirection_to_impact :
        config.incoming.origin - config.impact =
          d • (-config.incoming.direction) := by
      rw [← hd_impact]
      simp [LightRay.pointAt]
    have hangle :
        InnerProductGeometry.angle (-config.incoming.direction) n₁ = θ := by
      have hangle_readout := config.incidence_angle_readout
      rw [EuclideanGeometry.angle] at hangle_readout
      simp only [vsub_eq_sub, add_sub_cancel_right] at hangle_readout
      rw [hdirection_to_impact,
        InnerProductGeometry.angle_smul_left_of_pos _ _ hd_pos] at hangle_readout
      simpa [n₁, θ] using hangle_readout
    have hincoming_inner :
        @inner ℝ Space _ config.incoming.direction n₁ = -Real.cos θ := by
      have hunit_neg : ‖-config.incoming.direction‖ = 1 := by
        simpa using config.incoming.direction_is_unit
      have hinner :=
        InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
          hunit_neg config.mirror1.normal_is_unit
      rw [hangle] at hinner
      rw [inner_neg_left] at hinner
      dsimp [n₁] at *
      linarith
    letI : Nonempty config.mirror1.surface := config.mirror1.surface_nonempty
    have hreflect_linear :
        config.reflected.direction =
          config.mirror1.surface.direction.reflection config.incoming.direction := by
      rw [hreflected_direction]
      simp [PlaneMirror.reflectDirection,
        EuclideanGeometry.reflection_apply_of_mem _ _ himpact₁, vsub_eq_sub]
    have hn₁_orthogonal :
        n₁ ∈ config.mirror1.surface.directionᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [real_inner_comm]
      exact (config.mirror1.mem_direction_iff_inner_normal_zero u).1 hu
    have hreflect_n₁ :
        config.mirror1.surface.direction.reflection n₁ = -n₁ :=
      Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hn₁_orthogonal
    have hreflect_inner :
        @inner ℝ Space _
            (config.mirror1.surface.direction.reflection config.incoming.direction) n₁ =
          -@inner ℝ Space _ config.incoming.direction n₁ := by
      have hmap :=
        config.mirror1.surface.direction.reflection.inner_map_map
          config.incoming.direction n₁
      rw [hreflect_n₁] at hmap
      simp only [inner_neg_right] at hmap
      linarith
    rw [hreflect_linear, hreflect_inner, hincoming_inner]
    ring
  have hb_norm : ‖b‖ = t * Real.cos θ := by
    have hw_eq : w = b - a := by simp [w, a, b]
    have hw_inner :
        @inner ℝ Space _ w n₁ = t * Real.cos θ := by
      rw [hw, inner_smul_left, ht_cos]
      simp
    have hb_coefficient :
        @inner ℝ Space _ n₁ b = t * Real.cos θ := by
      rw [hw_eq, inner_sub_left, ha_inner_n₁, sub_zero] at hw_inner
      simpa [real_inner_comm] using hw_inner
    have hcos_pos : 0 < Real.cos θ := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> dsimp [θ, degrees] <;> nlinarith [Real.pi_pos]
    rw [hb_parallel_n₁, norm_smul, config.mirror1.normal_is_unit, mul_one,
      Real.norm_eq_abs, hb_coefficient, abs_of_pos (mul_pos ht hcos_pos)]
  have hab_inner : @inner ℝ Space _ a b = 0 := by
    rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simpa [EuclideanGeometry.angle, a, b, vsub_eq_sub] using
      config.cross_section_is_right_at_corner
  have hpyth : ‖w‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have hw_eq : w = b - a := by simp [w, a, b]
    rw [hw_eq, norm_sub_pow_two_real]
    rw [real_inner_comm, hab_inner]
    ring
  have hsin_pos : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [θ, degrees]
      positivity
    · dsimp [θ, degrees]
      nlinarith only [Real.pi_pos]
  have ht_formula : t = (5 / 4 : ℝ) / Real.sin θ := by
    rw [hw_norm, ha_norm, hb_norm] at hpyth
    have htrig := Real.sin_sq_add_cos_sq θ
    have ht_nonneg : 0 ≤ t := ht.le
    have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
    have hmul_sq : (t * Real.sin θ) ^ 2 = (5 / 4 : ℝ) ^ 2 := by
      have hsin_sq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        linarith only [htrig]
      rw [mul_pow, hsin_sq]
      nlinarith only [hpyth]
    have hmul_nonneg : 0 ≤ t * Real.sin θ := mul_nonneg ht_nonneg hsin_nonneg
    have hmul : t * Real.sin θ = (5 / 4 : ℝ) := by
      nlinarith only [hmul_sq, hmul_nonneg]
    exact (eq_div_iff hsin_pos.ne').2 hmul
  have hdist :
      physicalDistance config.impact config.strike =
        metres ((5 / 4 : ℝ) / Real.sin (degrees 40)) := by
    change metres (dist config.impact config.strike) =
      metres ((5 / 4 : ℝ) / Real.sin (degrees 40))
    congr 1
    simpa [w, dist_eq_norm, norm_sub_rev, θ] using hw_norm.trans ht_formula
  refine ⟨hdist, ?_⟩
  rw [hdist]
  simpa [siMetres, metres, answerMetres, CarriesDimension.toDimensionful_apply_apply,
    one_div] using numerical_bound

end PhyXMiniProblems.Problem0002
