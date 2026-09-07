import Family8Grounding.Family8TubeJohnContractedLipschitzV1
import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import FamilyStickyGrounding.FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnContractedAxisLengthLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8TubeJohnUnitRescalingV2
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnWitnessPositiveRadiiV4
open Family8TubeJohnContractedLipschitzV1
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

noncomputable section

/-!
# A uniform lower bound for tube-John transformed unit directions

The contracted tube-John map used by the actual proxy construction is treated
directly.  The inner ellipsoid places two opposite semiaxis points inside the
source tube.  The elementary tube-diameter estimate therefore bounds every
John semiaxis by `3/2` when the tube radius is at most one.  A deliberately
coarse three-coordinate estimate then makes the inverse contracted map
`108`-Lipschitz, and hence every transformed unit axis has length at least
`1/108`.
-/

/-- Every semiaxis of a John witness for a radius-at-most-one tube is at most
`3/2`.  This is derived from the witness's inner ellipsoid and the literal
tube diameter, rather than supplied as an extra certificate field. -/
theorem JohnAxisWitness.radius_le_three_halves_of_tube
    {rho : NNReal} (T : Tube rho) (hrhoOne : rho <= 1)
    (w : JohnAxisWitness T.body) (i : Fin 3) :
    (w.radius i : Real) <= 3 / 2 := by
  let p : Space := w.center + (w.radius i : Real) • w.frame i
  let q : Space := w.center - (w.radius i : Real) • w.frame i
  have hpEllipsoid : p ∈ axisEllipsoid w.center w.frame w.radius 1 := by
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
    · simp
    · dsimp only [p]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _hj hji
        simp [hji]
      · simp
  have hqEllipsoid : q ∈ axisEllipsoid w.center w.frame w.radius 1 := by
    refine ⟨fun j => if j = i then -1 else 0, ?_, ?_⟩
    · simp
    · dsimp only [q]
      rw [sub_eq_add_neg]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _hj hji
        simp [hji]
      · simp
  have hp : p ∈ T.carrier := by
    simpa only [Tube.coe_body] using w.inner hpEllipsoid
  have hq : q ∈ T.carrier := by
    simpa only [Tube.coe_body] using w.inner hqEllipsoid
  have hdiam : dist p q <= 1 + 2 * (rho : Real) :=
    dist_le_one_add_two_mul_radius_of_mem_tube_carrier T hp hq
  have hpq : dist p q = 2 * (w.radius i : Real) := by
    rw [dist_eq_norm]
    have hsub : p - q = (2 * (w.radius i : Real)) • w.frame i := by
      dsimp only [p, q]
      module
    rw [hsub, norm_smul, w.frame.norm_eq_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hrhoReal : (rho : Real) <= 1 := by exact_mod_cast hrhoOne
  rw [hpq] at hdiam
  linarith

/-- Before the final scalar contraction, the inverse John normalization is
`27/2`-Lipschitz.  The factor three is the explicit sum over the three
orthonormal coordinates, and each inverse coordinate coefficient is at most
`3 * (3/2) = 9/2`. -/
theorem axisEllipsoidNormalizationAffineEquiv_symm_dist_le_twentySeven_halves
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (w : JohnAxisWitness T.body) (y z : Space) :
    dist
        ((axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => JohnAxisWitness.radius_pos_of_tube T hrho w i)).symm y)
        ((axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => JohnAxisWitness.radius_pos_of_tube T hrho w i)).symm z) <=
      (27 / 2 : Real) * dist y z := by
  rw [dist_eq_norm]
  simp only [axisEllipsoidNormalizationAffineEquiv_symm_apply]
  have hsub :
      (w.center + ∑ i, ((3 * (w.radius i : Real)) *
            ⟪w.frame i, y⟫_Real) • w.frame i) -
          (w.center + ∑ i, ((3 * (w.radius i : Real)) *
            ⟪w.frame i, z⟫_Real) • w.frame i) =
        ∑ i, ((3 * (w.radius i : Real)) *
          ⟪w.frame i, y - z⟫_Real) • w.frame i := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [inner_sub_right]
    module
  rw [hsub]
  calc
    ‖∑ i, ((3 * (w.radius i : Real)) *
        ⟪w.frame i, y - z⟫_Real) • w.frame i‖ <=
        ∑ i, ‖((3 * (w.radius i : Real)) *
          ⟪w.frame i, y - z⟫_Real) • w.frame i‖ := norm_sum_le _ _
    _ <= ∑ _i : Fin 3, (9 / 2 : Real) * ‖y - z‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, w.frame.norm_eq_one, mul_one, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (by positivity :
          0 <= 3 * (w.radius i : Real))]
      have hradius := JohnAxisWitness.radius_le_three_halves_of_tube
        T hrhoOne w i
      have hinner := abs_real_inner_le_norm (w.frame i) (y - z)
      rw [w.frame.norm_eq_one, one_mul] at hinner
      exact mul_le_mul (by nlinarith) hinner (abs_nonneg _)
        (by positivity)
    _ = (27 / 2 : Real) * ‖y - z‖ := by
      rw [Fin.sum_univ_three]
      ring
    _ = (27 / 2 : Real) * dist y z := by rw [dist_eq_norm]

/-- The inverse of the actual contracted tube-John map is globally
`108`-Lipschitz on the full radius-at-most-one window. -/
theorem contractedTubeJohnAffineEquiv_symm_dist_le_oneHundredEight
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (w : JohnAxisWitness T.body) (y z : Space) :
    dist ((contractedTubeJohnAffineEquiv T hrho w).symm y)
        ((contractedTubeJohnAffineEquiv T hrho w).symm z) <=
      108 * dist y z := by
  let R := axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
    (fun i => JohnAxisWitness.radius_pos_of_tube T hrho w i)
  let D := scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num)
  change dist (R.symm (D.symm y)) (R.symm (D.symm z)) <= _
  calc
    dist (R.symm (D.symm y)) (R.symm (D.symm z)) <=
        (27 / 2 : Real) * dist (D.symm y) (D.symm z) := by
      exact axisEllipsoidNormalizationAffineEquiv_symm_dist_le_twentySeven_halves
        T hrho hrhoOne w (D.symm y) (D.symm z)
    _ = (27 / 2 : Real) * (8 * dist y z) := by
      dsimp only [D]
      rw [scalarDilationAffineEquiv_symm_apply,
        scalarDilationAffineEquiv_symm_apply, dist_smul₀,
        Real.norm_eq_abs]
      norm_num [NNReal.coe_inv]
    _ = 108 * dist y z := by ring

/-- Every unit direction has contracted tube-John linear image of norm at
least `1/108`. -/
theorem one_div_oneHundredEight_le_norm_contractedTubeJohn_linear
    {rho : NNReal} (P : Tube rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (w : JohnAxisWitness P.body) (v : Space) (hv : ‖v‖ = 1) :
    (1 / 108 : Real) <= ‖(contractedTubeJohnAffineEquiv P hrho w).linear v‖ := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hinv := contractedTubeJohnAffineEquiv_symm_dist_le_oneHundredEight
    P hrho hrhoOne w (e v) (e 0)
  rw [e.symm_apply_apply, e.symm_apply_apply] at hinv
  have himageDist : dist (e v) (e 0) = ‖e.linear v‖ := by
    rw [dist_eq_norm]
    have hsub : e v - e 0 = e.linear v := by
      rw [show v = v +ᵥ (0 : Space) by simp, e.map_vadd]
      simp
    rw [hsub]
  rw [dist_zero_right, himageDist, hv] at hinv
  nlinarith

/-- Specialization to the transformed endpoint vector used by every genuine
contracted-John proxy tube. -/
theorem one_div_oneHundredEight_le_norm_affineImageAxisVector_contracted
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body) (T : Tube delta) :
    (1 / 108 : Real) <=
      ‖affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) T‖ := by
  rw [affineImageAxisVector_eq_linear]
  exact one_div_oneHundredEight_le_norm_contractedTubeJohn_linear
    P hrho hrhoOne w T.axis.direction T.axis.norm_direction

#print axioms JohnAxisWitness.radius_le_three_halves_of_tube
#print axioms axisEllipsoidNormalizationAffineEquiv_symm_dist_le_twentySeven_halves
#print axioms contractedTubeJohnAffineEquiv_symm_dist_le_oneHundredEight
#print axioms one_div_oneHundredEight_le_norm_contractedTubeJohn_linear
#print axioms one_div_oneHundredEight_le_norm_affineImageAxisVector_contracted

end
end Family8TubeJohnContractedAxisLengthLowerV1
