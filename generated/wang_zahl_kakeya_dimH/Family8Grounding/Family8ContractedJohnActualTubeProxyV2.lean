import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnActualTubeProxyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8TubeJohnContractedLipschitzV1
open Family8ContractedJohnActualTubeProxyV1

noncomputable section

/-!
# Unit-ball support of contracted John tube proxies, V2

The common contracted John map places both endpoints of every child axis in
the radius-`1/8` ball.  Consequently the centered unit-axis extension lies
in the radius-`5/8` ball.  When the child scale is at most the parent scale,
the genuine proxy radius is at most `3/8`, so the entire actual proxy tube is
contained in the unit ball.  These are geometric consequences, not Frostman
or selection premises.
-/

/-- The center of the transformed child axis lies in the radius-`1/8` ball. -/
theorem norm_affineImageAxisCenter_contracted_le_eighth
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) :
    ‖affineImageAxisCenter (contractedTubeJohnAffineEquiv P hrho w) T‖ <=
      (1 / 8 : Real) := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hbaseParent : T.axis.base ∈ P.carrier :=
    hTP (T.axis_subset_carrier T.axis.base_mem_carrier)
  have hendParent : T.axis.endpoint ∈ P.carrier :=
    hTP (T.axis_subset_carrier T.axis.endpoint_mem_carrier)
  have hbase := image_parent_carrier_subset_closedBall_eighth
    P hrho w ⟨T.axis.base, hbaseParent, rfl⟩
  have hend := image_parent_carrier_subset_closedBall_eighth
    P hrho w ⟨T.axis.endpoint, hendParent, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hbase hend
  change ‖(1 / 2 : Real) • (e T.axis.base + e T.axis.endpoint)‖ <=
    (1 / 8 : Real)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
  calc
    (1 / 2 : Real) * ‖e T.axis.base + e T.axis.endpoint‖ <=
        (1 / 2 : Real) * (‖e T.axis.base‖ + ‖e T.axis.endpoint‖) := by
      gcongr
      exact norm_add_le _ _
    _ <= (1 / 2 : Real) * ((1 / 8 : Real) + (1 / 8 : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (by simpa only [e] using hbase)
          (by simpa only [e] using hend)) (by norm_num)
    _ = (1 / 8 : Real) := by norm_num

/-- The centered unit-axis extension of the contracted image lies in the
radius-`5/8` ball. -/
theorem affineImageUnitExtensionAxis_contracted_subset_fiveEighthsBall
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) :
    (affineImageUnitExtensionAxis
      (contractedTubeJohnAffineEquiv P hrho w) T).carrier ⊆
        Metric.closedBall (0 : Space) (5 / 8 : Real) := by
  intro x hx
  rw [UnitSegment.carrier_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hcenter := norm_affineImageAxisCenter_contracted_le_eighth
    P hrho w T hTP
  have hoffset :
      ‖(t - 1 / 2 : Real) • affineImageAxisDirection e T‖ <=
        (1 / 2 : Real) := by
    rw [norm_smul, norm_affineImageAxisDirection,
      mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hpoint :
      (affineImageUnitExtensionAxis e T).base +
          t • (affineImageUnitExtensionAxis e T).direction =
        affineImageAxisCenter e T +
          (t - 1 / 2 : Real) • affineImageAxisDirection e T := by
    simp only [affineImageUnitExtensionAxis_base,
      affineImageUnitExtensionAxis_direction]
    module
  change ‖(affineImageUnitExtensionAxis e T).base +
    t • (affineImageUnitExtensionAxis e T).direction‖ <= (5 / 8 : Real)
  rw [hpoint]
  calc
    ‖affineImageAxisCenter e T +
        (t - 1 / 2 : Real) • affineImageAxisDirection e T‖ <=
      ‖affineImageAxisCenter e T‖ +
        ‖(t - 1 / 2 : Real) • affineImageAxisDirection e T‖ :=
          norm_add_le _ _
    _ <= (1 / 8 : Real) + (1 / 2 : Real) := by
      exact add_le_add (by simpa only [e] using hcenter) hoffset
    _ = (5 / 8 : Real) := by norm_num

/-- The genuine proxy radius is at most `3/8` at a nested pair of scales. -/
theorem contractedJohnProxyRadius_le_threeEighths
    {delta rho : NNReal} (hdeltaRho : delta <= rho) (hrho : 0 < rho) :
    (contractedJohnProxyRadius delta rho : Real) <= (3 / 8 : Real) := by
  have hdeltaRhoReal : (delta : Real) <= (rho : Real) :=
    NNReal.coe_le_coe.mpr hdeltaRho
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrho
  simp only [contractedJohnProxyRadius, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_ofNat]
  rw [div_le_iff₀ (by positivity : (0 : Real) < 8 * (rho : Real))]
  nlinarith

/-- Every actual contracted-John proxy tube is supported in the unit ball. -/
theorem contractedJohnProxyTube_carrier_subset_unitBall
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) (hdeltaRho : delta <= rho) :
    (contractedJohnProxyTube P hrho w T).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  have haxis :=
    affineImageUnitExtensionAxis_contracted_subset_fiveEighthsBall
      P hrho w T hTP
  have hradius :=
    contractedJohnProxyRadius_le_threeEighths hdeltaRho hrho
  change Metric.cthickening (contractedJohnProxyRadius delta rho : Real)
      (affineImageUnitExtensionAxis
        (contractedTubeJohnAffineEquiv P hrho w) T).carrier ⊆
    Metric.closedBall (0 : Space) 1
  refine (Metric.cthickening_subset_of_subset _ haxis).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact Metric.closedBall_subset_closedBall (by linarith)

#print axioms norm_affineImageAxisCenter_contracted_le_eighth
#print axioms affineImageUnitExtensionAxis_contracted_subset_fiveEighthsBall
#print axioms contractedJohnProxyRadius_le_threeEighths
#print axioms contractedJohnProxyTube_carrier_subset_unitBall

end

end Family8ContractedJohnActualTubeProxyV2
