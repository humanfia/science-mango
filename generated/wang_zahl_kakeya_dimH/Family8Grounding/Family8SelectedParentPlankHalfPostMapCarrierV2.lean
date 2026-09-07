import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped NNReal

namespace Family8SelectedParentPlankHalfPostMapCarrierV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8

noncomputable section

def halfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) :
    Space ≃ᵃ[Real] Space :=
  (bucketNormalizedAffineEquiv e label).trans
    (scalarDilationAffineEquiv (2 : NNReal)⁻¹ (by norm_num))

@[simp] theorem halfPostBucketAffineEquiv_apply
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) (x : Space) :
    halfPostBucketAffineEquiv e label x =
      (1 / 2 : Real) • bucketNormalizedAffineEquiv e label x := by
  rw [halfPostBucketAffineEquiv, AffineEquiv.trans_apply,
    scalarDilationAffineEquiv_apply]
  norm_num

theorem affineImageAxisVector_halfPostBucketAffineEquiv
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int)
    (T : Tube delta) :
    affineImageAxisVector (halfPostBucketAffineEquiv e label) T =
      (1 / 2 : Real) •
        affineImageAxisVector (bucketNormalizedAffineEquiv e label) T := by
  unfold affineImageAxisVector
  simp only [halfPostBucketAffineEquiv_apply]
  module

theorem norm_affineImageAxisVector_halfPostBucketAffineEquiv
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int)
    (T : Tube delta) :
    ‖affineImageAxisVector (halfPostBucketAffineEquiv e label) T‖ =
      (1 / 2 : Real) *
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label) T‖ := by
  rw [affineImageAxisVector_halfPostBucketAffineEquiv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]

#print axioms halfPostBucketAffineEquiv_apply
#print axioms affineImageAxisVector_halfPostBucketAffineEquiv
#print axioms norm_affineImageAxisVector_halfPostBucketAffineEquiv

end
end Family8SelectedParentPlankHalfPostMapCarrierV2
