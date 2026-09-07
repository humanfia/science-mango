import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Family8Grounding.Family8StickyFiberContractedJohnProxyKatzTaoV2
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankFineProxyKatzTaoV3

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
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Katz--Tao transport to the literal selected-plank fine proxy, V3

The proved carrier bridge is combined with tube-volume comparison and affine
preimages.  The output is an actual `IsKatzTao` theorem for the same literal
proxy family used by normalized fresh selection.
-/

def affineAxisProxyVolumeRatio (delta s : NNReal) : ENNReal :=
  (8 * (s : ENNReal) ^ 2) / ((delta : ENNReal) ^ 2 / 2)

def selectedPlankFineProxyKatzTaoConstant
    (delta s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (C : ENNReal) : ENNReal :=
  affineAxisProxyVolumeRatio delta s * C / affineJacobian e

theorem affineAxisProxyTube_volume_le_ratio_mul_source
    {delta s : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsHalf : s ≤ (2 : NNReal)⁻¹) :
    volume (affineAxisProxyTube s e T).carrier ≤
      affineAxisProxyVolumeRatio delta s * volume T.carrier := by
  let floor : ENNReal := (delta : ENNReal) ^ 2 / 2
  let upper : ENNReal := 8 * (s : ENNReal) ^ 2
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (by norm_num)
  have hupper : volume (affineAxisProxyTube s e T).carrier ≤ upper := by
    exact (affineAxisProxyTube s e T).volume_le_eight_mul_sq_of_le_half
      hsHalf
  have hlower : floor ≤ volume T.carrier := by
    exact T.half_sq_le_volume_of_le_half hdeltaHalf
  calc
    volume (affineAxisProxyTube s e T).carrier ≤ upper := hupper
    _ = (upper / floor) * floor := by
      rw [ENNReal.div_mul_cancel hfloor0 hfloorTop]
    _ ≤ (upper / floor) * volume T.carrier := by gcongr
    _ = affineAxisProxyVolumeRatio delta s * volume T.carrier := by rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedPlankFineSourceFamily_isKatzTao_of_global
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily) :
    IsKatzTao C
      (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) := by
  let Y := emptyShading fine
  exact stickyFiberSourceFamily_isKatzTao_of_global
    S Y W.1.1.1 hKT

/-- Honest affine-preimage transport from the global fine family to the
literal proxy family on the same selected parent fibre. -/
theorem selectedPlankFineProxyFamily_isKatzTao_of_global
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    IsKatzTao
      (selectedPlankFineProxyKatzTaoConstant delta s
        (bucketNormalizedAffineEquiv e label) C)
      (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily := by
  classical
  intro K
  unfold IsKatzTaoAt
  let E := bucketNormalizedAffineEquiv e label
  let Kpre : ConvexBody Space := affinePreimageConvexBody E K
  let ratio : ENNReal := affineAxisProxyVolumeRatio delta s
  have hsource : IsKatzTao C
      (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) :=
    selectedPlankFineSourceFamily_isKatzTao_of_global
      e S B hrho label W hKT
  have hsubset :
      containedIndices
          (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily K ⊆
        containedIndices
          (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) Kpre := by
    intro i hi
    rw [mem_containedIndices] at hi ⊢
    change (fine.tubes i.1).carrier ⊆ E.symm '' (K : Set Space)
    apply (affineImage_subset_iff_subset_preimage
      E (fine.tubes i.1).carrier (K : Set Space)).mp
    change (affineAxisProxyTube s E (fine.tubes i.1)).carrier ⊆
      (K : Set Space) at hi
    exact (image_tubeCarrier_subset_affineAxisProxyTube
      E (fine.tubes i.1) (haxisLength i) hradius).trans hi
  have hJ0 : affineJacobian E ≠ 0 := (affineJacobian_pos E).ne'
  have hJTop : affineJacobian E ≠ ∞ := affineJacobian_ne_top E
  calc
    containedMass
        (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily K =
      ∑ i ∈ containedIndices
          (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily K,
        volume ((selectedPlankFineProxyFamily
          s e S B hrho label W).tubes i).carrier := by rfl
    _ ≤ ∑ i ∈ containedIndices
          (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily K,
        ratio * volume (fine.tubes i.1).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact affineAxisProxyTube_volume_le_ratio_mul_source
        E (fine.tubes i.1) hdeltaPos hdeltaHalf hsHalf
    _ = ratio *
        ∑ i ∈ containedIndices
          (selectedPlankFineProxyFamily s e S B hrho label W).bodyFamily K,
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
    _ = selectedPlankFineProxyKatzTaoConstant delta s E C *
        volume (K : Set Space) := by
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

#print axioms affineAxisProxyTube_volume_le_ratio_mul_source
#print axioms selectedPlankFineSourceFamily_isKatzTao_of_global
#print axioms selectedPlankFineProxyFamily_isKatzTao_of_global

end
end Family8SelectedParentPlankFineProxyKatzTaoV3
