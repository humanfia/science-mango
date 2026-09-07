import Family8Grounding.Family8TubeJohnWitnessPositiveRadiiV4
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnContractedLipschitzV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnUnitRescalingV2
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnWitnessPositiveRadiiV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5

noncomputable section

/-!
# Quantitative Lipschitz control for the contracted tube-John map

The outer ellipsoid of an honest John witness for a positive-radius tube
cannot have an arbitrarily short semiaxis: two opposite radius points of the
tube force `rho <= 3 * radius i`.  This turns the already constructed John
normalization, followed by the common scalar contraction `1/8`, into a
callback-free `3 / (8*rho)` Lipschitz map.  This is the geometric input for
constructing genuine normalized tube proxies for one parent fibre.
-/

/-- Every semiaxis of a genuine tube John witness is at least `rho / 3`.
This is quantitative information derived from the witness's outer
containment, not an additional field or premise. -/
theorem JohnAxisWitness.tubeRadius_le_three_mul_radius
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) (i : Fin 3) :
    rho <= 3 * w.radius i := by
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
  rcases w.outer hpBody with ⟨zp, hzp, hpEq⟩
  rcases w.outer hqBody with ⟨zq, hzq, hqEq⟩
  have hzpSq : (zp i) ^ 2 <= 9 := by
    calc
      (zp i) ^ 2 <= ∑ j, (zp j) ^ 2 := by
        exact Finset.single_le_sum (fun j _hj => sq_nonneg (zp j))
          (Finset.mem_univ i)
      _ <= (3 : Real) ^ 2 := hzp
      _ = 9 := by norm_num
  have hzqSq : (zq i) ^ 2 <= 9 := by
    calc
      (zq i) ^ 2 <= ∑ j, (zq j) ^ 2 := by
        exact Finset.single_le_sum (fun j _hj => sq_nonneg (zq j))
          (Finset.mem_univ i)
      _ <= (3 : Real) ^ 2 := hzq
      _ = 9 := by norm_num
  have hzpAbs : |zp i| <= 3 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hzqAbs : |zq i| <= 3 := by
    rw [abs_le]
    constructor <;> nlinarith
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
  have hdiffAbs : |zp i - zq i| <= 6 := by
    calc
      |zp i - zq i| <= |zp i| + |zq i| := abs_sub _ _
      _ <= 3 + 3 := add_le_add hzpAbs hzqAbs
      _ = 6 := by norm_num
  have heq :
      2 * (rho : Real) =
        (zp i - zq i) * (w.radius i : Real) := by
    linarith [hpcoord, hqcoord, hpqcoord]
  have htwo :
      2 * (rho : Real) <= 6 * (w.radius i : Real) := by
    calc
      2 * (rho : Real) =
          |(zp i - zq i) * (w.radius i : Real)| := by
        rw [← heq, abs_of_pos (by positivity : 0 < 2 * (rho : Real))]
      _ = |zp i - zq i| * (w.radius i : Real) := by
        rw [abs_mul, abs_of_nonneg NNReal.zero_le_coe]
      _ <= 6 * (w.radius i : Real) := by gcongr
  exact_mod_cast (by linarith : (rho : Real) <= 3 * (w.radius i : Real))

/-- The uncontracted John normalization of a radius-`rho` tube has the safe
global Lipschitz constant `3/rho`. -/
theorem axisEllipsoidNormalizationAffineEquiv_dist_le
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) (x y : Space) :
    dist
        (axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i) x)
        (axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i) y) <=
      (3 / (rho : Real)) * dist x y := by
  let hrad : ∀ i, 0 < w.radius i :=
    fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i
  let R := axisEllipsoidNormalizationAffineEquiv
    w.center w.frame w.radius hrad
  rw [dist_eq_norm]
  have hdiff :
      R x - R y =
        ∑ i, (⟪w.frame i, x - y⟫_Real /
          (3 * (w.radius i : Real))) • w.frame i := by
    dsimp only [R]
    rw [axisEllipsoidNormalizationAffineEquiv_apply,
      axisEllipsoidNormalizationAffineEquiv_apply,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← sub_smul]
    congr 1
    rw [← sub_div, ← inner_sub_right]
    congr 2
    abel
  rw [hdiff]
  calc
    ‖∑ i, (⟪w.frame i, x - y⟫_Real /
          (3 * (w.radius i : Real))) • w.frame i‖ <=
        ∑ i, ‖(⟪w.frame i, x - y⟫_Real /
          (3 * (w.radius i : Real))) • w.frame i‖ :=
      norm_sum_le _ _
    _ <= ∑ _i : Fin 3, ‖x - y‖ / (rho : Real) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, w.frame.norm_eq_one, mul_one, Real.norm_eq_abs,
        abs_div, abs_of_pos (mul_pos (by norm_num)
          (NNReal.coe_pos.mpr (hrad i)))]
      have hinner := abs_real_inner_le_norm (w.frame i) (x - y)
      rw [w.frame.norm_eq_one, one_mul] at hinner
      have hradius : (rho : Real) <= 3 * (w.radius i : Real) := by
        exact_mod_cast Family8TubeJohnContractedLipschitzV1.JohnAxisWitness.tubeRadius_le_three_mul_radius T hrho w i
      apply (div_le_div_iff₀
        (mul_pos (by norm_num) (NNReal.coe_pos.mpr (hrad i)))
        (NNReal.coe_pos.mpr hrho)).2
      exact mul_le_mul hinner hradius NNReal.zero_le_coe (norm_nonneg _)
    _ = (3 / (rho : Real)) * ‖x - y‖ := by
      rw [Fin.sum_univ_three]
      field_simp
      ring

/-- The common tube-John normalization followed by scalar contraction
`1/8`. -/
noncomputable def contractedTubeJohnAffineEquiv
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) : Space ≃ᵃ[Real] Space :=
  (axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
      (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i)).trans
    (scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num))

@[simp]
theorem contractedTubeJohnAffineEquiv_apply
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) (x : Space) :
    contractedTubeJohnAffineEquiv T hrho w x =
      (1 / 8 : Real) •
        axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i) x := by
  simp [contractedTubeJohnAffineEquiv,
    scalarDilationAffineEquiv_apply]

/-- The contracted tube-John map has the exact scale-ratio Lipschitz bound
needed for an actual radius-`3*delta/(8*rho)` tube proxy. -/
theorem contractedTubeJohnAffineEquiv_dist_le
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness T.body) (x y : Space) :
    dist (contractedTubeJohnAffineEquiv T hrho w x)
        (contractedTubeJohnAffineEquiv T hrho w y) <=
      (3 / (8 * (rho : Real))) * dist x y := by
  rw [contractedTubeJohnAffineEquiv_apply,
    contractedTubeJohnAffineEquiv_apply, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
  have h := axisEllipsoidNormalizationAffineEquiv_dist_le
    T hrho w x y
  calc
    (1 / 8 : Real) * dist
        (axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i) x)
        (axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i => Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube T hrho w i) y) <=
      (1 / 8 : Real) * ((3 / (rho : Real)) * dist x y) := by gcongr
    _ = (3 / (8 * (rho : Real))) * dist x y := by
      field_simp

#print axioms JohnAxisWitness.tubeRadius_le_three_mul_radius
#print axioms axisEllipsoidNormalizationAffineEquiv_dist_le
#print axioms contractedTubeJohnAffineEquiv_apply
#print axioms contractedTubeJohnAffineEquiv_dist_le

end
end Family8TubeJohnContractedLipschitzV1
