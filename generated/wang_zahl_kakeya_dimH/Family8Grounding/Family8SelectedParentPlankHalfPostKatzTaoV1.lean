import Family8Grounding.Family8SelectedParentPlankHalfPostMapCarrierV3
import Family8Grounding.Family8SelectedParentPlankFineProxyKatzTaoV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankHalfPostKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8SelectedParentPlankHalfPostMapCarrierV2
open Family8SelectedParentPlankHalfPostMapCarrierV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Katz--Tao transport after the selected-bucket half post-map

The bucket and selected-parent subtype remain unchanged.  Only after the
common bucket map do we postcompose scalar dilation by `1/2`.  The actual
selected-plank carrier theorem then supplies the unit-axis hypothesis
automatically, so Katz--Tao transport has no axis-length callback.
-/

def halfPostSelectedPlankFineProxyKatzTaoConstant
    (delta s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (label : Fin 3 → Int) (C : ENNReal) : ENNReal :=
  selectedPlankFineProxyKatzTaoConstant delta s
    (halfPostBucketAffineEquiv e label) C

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Affine-preimage Katz--Tao transport for the literal half-post proxy
family.  The only geometric input left is the transverse-radius budget;
the longitudinal unit bound is obtained from the selected-parent plank. -/
theorem halfPostSelectedPlankFineProxyFamily_isKatzTao_of_global
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hradius : affineLinearOperatorNorm
      (halfPostBucketAffineEquiv e label) * (delta : Real) ≤ (s : Real)) :
    IsKatzTao
      (halfPostSelectedPlankFineProxyKatzTaoConstant delta s e label C)
      (halfPostSelectedPlankFineProxyFamily
        s e S B hrho label W).bodyFamily := by
  classical
  intro K
  unfold IsKatzTaoAt
  let E := halfPostBucketAffineEquiv e label
  let Kpre : ConvexBody Space := affinePreimageConvexBody E K
  let ratio : ENNReal := affineAxisProxyVolumeRatio delta s
  have hsource : IsKatzTao C
      (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) :=
    selectedPlankFineSourceFamily_isKatzTao_of_global
      e S B hrho label W hKT
  have hsubset :
      containedIndices
          (halfPostSelectedPlankFineProxyFamily
            s e S B hrho label W).bodyFamily K ⊆
        containedIndices
          (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) Kpre := by
    intro i hi
    rw [mem_containedIndices] at hi ⊢
    change (fine.tubes i.1).carrier ⊆ E.symm '' (K : Set Space)
    apply (affineImage_subset_iff_subset_preimage
      E (fine.tubes i.1).carrier (K : Set Space)).mp
    change (affineAxisProxyTube s E (fine.tubes i.1)).carrier ⊆
      (K : Set Space) at hi
    exact (halfPost_image_tubeCarrier_subset_proxy
      s e S B hrho label hplank W hradius i).trans hi
  have hJ0 : affineJacobian E ≠ 0 := (affineJacobian_pos E).ne'
  have hJTop : affineJacobian E ≠ ∞ := affineJacobian_ne_top E
  calc
    containedMass
        (halfPostSelectedPlankFineProxyFamily
          s e S B hrho label W).bodyFamily K =
      ∑ i ∈ containedIndices
          (halfPostSelectedPlankFineProxyFamily
            s e S B hrho label W).bodyFamily K,
        volume ((halfPostSelectedPlankFineProxyFamily
          s e S B hrho label W).tubes i).carrier := by rfl
    _ ≤ ∑ i ∈ containedIndices
          (halfPostSelectedPlankFineProxyFamily
            s e S B hrho label W).bodyFamily K,
        ratio * volume (fine.tubes i.1).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact affineAxisProxyTube_volume_le_ratio_mul_source
        E (fine.tubes i.1) hdeltaPos hdeltaHalf hsHalf
    _ = ratio *
        ∑ i ∈ containedIndices
          (halfPostSelectedPlankFineProxyFamily
            s e S B hrho label W).bodyFamily K,
        volume (fine.tubes i.1).carrier := by rw [Finset.mul_sum]
    _ ≤ ratio *
        ∑ i ∈ containedIndices
          (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) Kpre,
        volume (fine.tubes i.1).carrier := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset hsubset) bot_le
    _ = ratio * containedMass
        (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) Kpre := by
      rfl
    _ ≤ ratio * (C * volume (Kpre : Set Space)) := by
      exact mul_le_mul_of_nonneg_left (hsource Kpre) bot_le
    _ = halfPostSelectedPlankFineProxyKatzTaoConstant
          delta s e label C * volume (K : Set Space) := by
      rw [volume_eq_affineJacobian_mul_preimage E K]
      change ratio * (C * volume (Kpre : Set Space)) =
        (ratio * C / affineJacobian E) *
          (affineJacobian E * volume (Kpre : Set Space))
      calc
        ratio * (C * volume (Kpre : Set Space)) =
            (ratio * C) * volume (Kpre : Set Space) := by ac_rfl
        _ = ((ratio * C / affineJacobian E) * affineJacobian E) *
              volume (Kpre : Set Space) := by
          rw [ENNReal.div_mul_cancel hJ0 hJTop]
        _ = (ratio * C / affineJacobian E) *
              (affineJacobian E * volume (Kpre : Set Space)) := by ac_rfl

#print axioms halfPostSelectedPlankFineProxyKatzTaoConstant
#print axioms halfPostSelectedPlankFineProxyFamily_isKatzTao_of_global

end
end Family8SelectedParentPlankHalfPostKatzTaoV1
