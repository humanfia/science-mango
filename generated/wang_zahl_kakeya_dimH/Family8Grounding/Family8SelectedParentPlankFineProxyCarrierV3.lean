import Family8Grounding.Family8SelectedParentPlankFineProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal

namespace Family8SelectedParentPlankFineProxyCarrierV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentPlankFineProxyDatumV1

noncomputable section

/-!
# Literal affine-axis proxy carrier containment

This isolates the exact two geometric conditions under which a common affine
image of an actual tube is contained in the unit-axis proxy used by fresh
selection: the transformed axis must fit in the unit extension, and the proxy
radius must pay the operator-norm amplification of the source radius.
-/

noncomputable def affineLinearOperatorNorm
    (e : Space ≃ᵃ[Real] Space) : Real :=
  ‖LinearMap.toContinuousLinearMap e.linear.toLinearMap‖

theorem affineLinear_norm_le
    (e : Space ≃ᵃ[Real] Space) (v : Space) :
    ‖e.linear v‖ ≤ affineLinearOperatorNorm e * ‖v‖ := by
  exact ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap e.linear.toLinearMap) v

theorem affine_apply_sub_affine_apply
    (e : Space ≃ᵃ[Real] Space) (x a : Space) :
    e x - e a = e.linear (x - a) := by
  calc
    e x - e a = e ((x - a) +ᵥ a) - e a := by
      simp only [vadd_eq_add]
      congr 2
      abel
    _ = (e.linear (x - a) +ᵥ e a) - e a := by
      rw [e.map_vadd]
    _ = e.linear (x - a) := by
      simp only [vadd_eq_add]
      abel

/-- The explicit longitudinal and transverse distortion budgets give the
literal source-carrier image containment needed for affine-preimage KT
transport. -/
theorem image_tubeCarrier_subset_affineAxisProxyTube
    {delta s : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (haxisLength : ‖affineImageAxisVector e T‖ ≤ 1)
    (hradius : affineLinearOperatorNorm e * (delta : Real) ≤ (s : Real)) :
    e '' T.carrier ⊆ (affineAxisProxyTube s e T).carrier := by
  have haxisImage : e '' T.axis.carrier ⊆
      (affineImageUnitExtensionAxis e T).carrier :=
    image_axis_carrier_subset_affineImageUnitExtensionAxis
      e T haxisLength
  rintro _ ⟨x, hx, rfl⟩
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (delta : Real) by positivity)] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨a, haAxis, hxa⟩ := hx
  have haProxy : e a ∈ (affineImageUnitExtensionAxis e T).carrier :=
    haxisImage ⟨a, haAxis, rfl⟩
  have hdistLinear :
      dist (e x) (e a) ≤ affineLinearOperatorNorm e * dist x a := by
    rw [dist_eq_norm, dist_eq_norm, affine_apply_sub_affine_apply]
    exact affineLinear_norm_le e (x - a)
  have hop : 0 ≤ affineLinearOperatorNorm e := norm_nonneg _
  have hdist : dist (e x) (e a) ≤ (s : Real) := by
    calc
      dist (e x) (e a) ≤
          affineLinearOperatorNorm e * dist x a := hdistLinear
      _ ≤ affineLinearOperatorNorm e * (delta : Real) :=
        mul_le_mul_of_nonneg_left hxa hop
      _ ≤ (s : Real) := hradius
  change e x ∈ Metric.cthickening (s : Real)
    (affineImageUnitExtensionAxis e T).carrier
  exact Metric.closedBall_subset_cthickening haProxy _ hdist

#print axioms affineLinear_norm_le
#print axioms affine_apply_sub_affine_apply
#print axioms image_tubeCarrier_subset_affineAxisProxyTube

end
end Family8SelectedParentPlankFineProxyCarrierV3
