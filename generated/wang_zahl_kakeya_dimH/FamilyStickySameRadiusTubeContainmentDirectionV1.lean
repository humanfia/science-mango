import FamilyStickyTubeParentDirectionCoherenceV1

set_option autoImplicit false

open Set
open scoped NNReal InnerProductSpace

namespace FamilyStickySameRadiusTubeContainmentDirectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Projective direction rigidity of same-radius tube containment

Two closed neighborhoods of unit segments have the same radius.  If one is
contained in the other, the two axis directions must agree up to reversal.
The proof uses the two diameter-extreme points of the child tube.  Pairing
them with points on the parent axis and testing their displacement against
the child unit direction forces equality in the unit-vector inner-product
bound.
-/

/-- Literal containment between tubes of the same radius forces zero
projective sine angle between their axis directions. -/
theorem Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ U.carrier) :
    Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction) = 0 := by
  let d : Real := (delta : Real)
  let p : Space := T.axis.base - d • T.axis.direction
  let q : Space := T.axis.endpoint + d • T.axis.direction
  have hd : 0 <= d := by positivity
  have hpDist : dist p T.axis.base <= d := by
    rw [dist_eq_norm]
    have hpSub : p - T.axis.base = -(d • T.axis.direction) := by
      dsimp only [p]
      module
    rw [hpSub, norm_neg, norm_smul, T.axis.norm_direction, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hd]
  have hqDist : dist q T.axis.endpoint <= d := by
    rw [dist_eq_norm]
    have hqSub : q - T.axis.endpoint = d • T.axis.direction := by
      dsimp only [q]
      module
    rw [hqSub, norm_smul, T.axis.norm_direction, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hd]
  have hpT : p ∈ T.carrier := by
    exact Metric.closedBall_subset_cthickening T.axis.base_mem_carrier d
      hpDist
  have hqT : q ∈ T.carrier := by
    exact Metric.closedBall_subset_cthickening T.axis.endpoint_mem_carrier d
      hqDist
  have hpU := hTU hpT
  have hqU := hTU hqT
  rw [Tube.carrier,
    U.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall hd] at hpU hqU
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hpU hqU
  obtain ⟨a, haAxis, hpa⟩ := hpU
  obtain ⟨b, hbAxis, hqb⟩ := hqU
  rw [U.axis.carrier_eq_image] at haAxis hbAxis
  obtain ⟨s, hs, rfl⟩ := haAxis
  obtain ⟨t, ht, rfl⟩ := hbAxis
  let u : Space := U.axis.direction
  let v : Space := T.axis.direction
  have hu : ‖u‖ = 1 := U.axis.norm_direction
  have hv : ‖v‖ = 1 := T.axis.norm_direction
  have hfirst : ⟪q - (U.axis.base + t • u), v⟫_ℝ <= d := by
    calc
      ⟪q - (U.axis.base + t • u), v⟫_ℝ <=
          ‖q - (U.axis.base + t • u)‖ * ‖v‖ :=
        real_inner_le_norm _ _
      _ = dist q (U.axis.base + t • u) := by
        rw [hv, mul_one, dist_eq_norm]
      _ <= d := hqb
  have hthird : ⟪(U.axis.base + s • u) - p, v⟫_ℝ <= d := by
    calc
      ⟪(U.axis.base + s • u) - p, v⟫_ℝ <=
          ‖(U.axis.base + s • u) - p‖ * ‖v‖ :=
        real_inner_le_norm _ _
      _ = dist p (U.axis.base + s • u) := by
        rw [hv, mul_one, dist_comm, dist_eq_norm]
      _ <= d := hpa
  have hst : |t - s| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hmiddle :
      ⟪(U.axis.base + t • u) - (U.axis.base + s • u), v⟫_ℝ <=
        |⟪u, v⟫_ℝ| := by
    have hsub :
        (U.axis.base + t • u) - (U.axis.base + s • u) =
          (t - s) • u := by module
    rw [hsub, real_inner_smul_left]
    calc
      (t - s) * ⟪u, v⟫_ℝ <= |(t - s) * ⟪u, v⟫_ℝ| :=
        le_abs_self _
      _ = |t - s| * |⟪u, v⟫_ℝ| := abs_mul _ _
      _ <= 1 * |⟪u, v⟫_ℝ| :=
        mul_le_mul_of_nonneg_right hst (abs_nonneg _)
      _ = |⟪u, v⟫_ℝ| := one_mul _
  have hlong : ⟪q - p, v⟫_ℝ = 1 + 2 * d := by
    have hqp : q - p = (1 + 2 * d) • v := by
      dsimp only [q, p, v]
      simp only [UnitSegment.endpoint]
      module
    rw [hqp, real_inner_smul_left, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one]
  have hdecomp :
      ⟪q - p, v⟫_ℝ =
        ⟪q - (U.axis.base + t • u), v⟫_ℝ +
        ⟪(U.axis.base + t • u) - (U.axis.base + s • u), v⟫_ℝ +
        ⟪(U.axis.base + s • u) - p, v⟫_ℝ := by
    rw [← inner_add_left, ← inner_add_left]
    congr 1
    module
  have hinnerLower : 1 <= |⟪u, v⟫_ℝ| := by
    rw [hdecomp] at hlong
    linarith
  have hinnerUpper : |⟪u, v⟫_ℝ| <= 1 := by
    simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v
  have hinnerAbs : |⟪u, v⟫_ℝ| = 1 :=
    le_antisymm hinnerUpper hinnerLower
  have hcosAbs :
      |Real.cos (InnerProductGeometry.angle u v)| = 1 := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hu hv]
      at hinnerAbs
    exact hinnerAbs
  have hcosSq := congrArg (fun x : Real => x ^ 2) hcosAbs
  rw [sq_abs] at hcosSq
  norm_num at hcosSq
  have htrig := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle u v)
  have hsin : Real.sin (InnerProductGeometry.angle u v) = 0 := by
    rcases hcosSq with hcos | hcos
    · rw [hcos] at htrig
      norm_num at htrig
      exact htrig
    · rw [hcos] at htrig
      norm_num at htrig
      exact htrig
  simpa only [u, v, InnerProductGeometry.angle_comm] using hsin

#print axioms Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset

end

end FamilyStickySameRadiusTubeContainmentDirectionV1
