import Family8Grounding.Family8TubeJohnOuterEllipsoidUnitBallV3

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnWitnessPositiveRadiiV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Positive semiaxes for any John witness of a positive-radius tube

The outer ellipsoid sees two opposite transverse points
obtained by adding and subtracting `rho * frame i` from `axis.base`.  Their coordinates differ by
`2 * rho`, so the corresponding semiaxis cannot vanish.
-/

/-- Every semiaxis of any John-axis witness for a positive-radius tube is
strictly positive. -/
theorem JohnAxisWitness.radius_pos_of_tube
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) (i : Fin 3) :
    0 < w.radius i := by
  let p : Space := T.axis.base + (rho : Real) • w.frame i
  let q : Space := T.axis.base - (rho : Real) • w.frame i
  have hpball : p ∈ Metric.closedBall T.axis.base (rho : Real) := by
    rw [Metric.mem_closedBall]
    simp [p, dist_eq_norm, norm_smul]
  have hqball : q ∈ Metric.closedBall T.axis.base (rho : Real) := by
    rw [Metric.mem_closedBall]
    simp [q, norm_smul]
  have hpTube : p ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
      (rho : Real) hpball
  have hqTube : q ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
      (rho : Real) hqball
  have hpBody : p ∈ (T.body : Set Space) := by
    simpa only [Tube.coe_body] using hpTube
  have hqBody : q ∈ (T.body : Set Space) := by
    simpa only [Tube.coe_body] using hqTube
  rcases w.outer hpBody with ⟨zp, _hzp, hpEq⟩
  rcases w.outer hqBody with ⟨zq, _hzq, hqEq⟩
  have hpcoord :
      ⟪w.frame i, p⟫_Real - ⟪w.frame i, w.center⟫_Real =
        zp i * (w.radius i : Real) := by
    rw [hpEq, inner_add_right, add_sub_cancel_left, inner_sum]
    simp only [real_inner_smul_right, w.frame.inner_eq_ite]
    simp
  have hqcoord :
      ⟪w.frame i, q⟫_Real - ⟪w.frame i, w.center⟫_Real =
        zq i * (w.radius i : Real) := by
    rw [hqEq, inner_add_right, add_sub_cancel_left, inner_sum]
    simp only [real_inner_smul_right, w.frame.inner_eq_ite]
    simp
  have hpqcoord :
      ⟪w.frame i, p⟫_Real - ⟪w.frame i, q⟫_Real =
        2 * (rho : Real) := by
    simp [p, q, inner_add_right, inner_sub_right,
      real_inner_smul_right]
    ring
  have hradiusNe : (w.radius i : Real) ≠ 0 := by
    intro hzero
    rw [hzero] at hpcoord hqcoord
    norm_num at hpcoord hqcoord
    have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrho
    nlinarith [hpqcoord]
  exact NNReal.coe_pos.mp
    (lt_of_le_of_ne NNReal.zero_le_coe (Ne.symm hradiusNe))

#print axioms JohnAxisWitness.radius_pos_of_tube

end
end Family8TubeJohnWitnessPositiveRadiiV4
