import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8Family7CriticalScaleProxyVolumeComparisonV1
import Family8Grounding.Family8FrostmanAmbientReplacementV2
import Family8Grounding.Family8FrostmanFamilyEnlargementV2
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CriticalScaleProxyFrostmanTransportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7CriticalScaleProxyVolumeComparisonV1
open Family8Family7CriticalScaleProxyVolumeLossV2
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8FrostmanAmbientReplacementV2
open Family8FrostmanFamilyEnlargementV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1

noncomputable section

universe u

/-!
# Frostman transport to the literal critical-scale round proxy, V3

V1 imported a failed family-enlargement draft. V2 omitted the namespace of
`affineImageAxisVector`. Neither predecessor is imported.
-/

theorem criticalScaleAffineProxyFamily_isFrostmanIn
    {radius : NNReal} {iota : Type u} [Fintype iota]
    (T : iota → Tube radius)
    (hradius : 0 < radius) (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real)
    (hproxyHalf : criticalScaleProxyRadius radius t ht ≤ (2 : NNReal)⁻¹)
    (haxis : ∀ i, ‖affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) (T i)‖ ≤ 1)
    (htransverse : affineLinearOperatorNorm
        (criticalScaleAffineEquiv t ht a0 b0 c0 d0) *
          (radius : Real) ≤
        (criticalScaleProxyRadius radius t ht : Real))
    (hproxyContained : ∀ i,
      (affineAxisProxyTube (criticalScaleProxyRadius radius t ht)
        (criticalScaleAffineEquiv t ht a0 b0 c0 d0) (T i)).carrier ⊆
          Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hsource : IsFrostmanIn C
      (fun i ↦ (T i).body) unitBallBody) :
    IsFrostmanIn
      (criticalScaleAffineProxyVolumeLoss *
        (affineJacobian
          (criticalScaleAffineEquiv t ht a0 b0 c0 d0).symm * C))
      (fun i ↦ (affineAxisProxyTube
        (criticalScaleProxyRadius radius t ht)
        (criticalScaleAffineEquiv t ht a0 b0 c0 d0) (T i)).body)
      unitBallBody := by
  let e := criticalScaleAffineEquiv t ht a0 b0 c0 d0
  let s := criticalScaleProxyRadius radius t ht
  let F : ConvexFamily iota := fun i ↦ (T i).body
  let Kpre := affinePreimageConvexBody e unitBallBody
  have himageSubset : ∀ i, e '' (T i).carrier ⊆
      (affineAxisProxyTube s e (T i)).carrier := by
    intro i
    exact image_tubeCarrier_subset_affineAxisProxyTube
      e (T i) (haxis i) htransverse
  have hsourcePre : ∀ i, (F i : Set Space) ⊆ (Kpre : Set Space) := by
    intro i x hx
    change x ∈ e.symm '' (unitBallBody : Set Space)
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    change e x ∈ Metric.closedBall (0 : Space) 1
    exact hproxyContained i (himageSubset i ⟨x, hx, rfl⟩)
  have hpreVolume : volume (Kpre : Set Space) ≤
      affineJacobian e.symm * volume (unitBallBody : Set Space) := by
    exact le_of_eq (volume_affineImageConvexBody e.symm unitBallBody)
  have hpre : IsFrostmanIn (affineJacobian e.symm * C) F Kpre :=
    isFrostmanIn_replace_ambient hsource hsourcePre hpreVolume
  have haffine := IsFrostmanIn.affineImage e hpre
  have hambient : affineImageConvexBody e Kpre = unitBallBody := by
    apply ConvexBody.ext
    exact image_affinePreimageConvexBody e unitBallBody
  have haffineUnit : IsFrostmanIn (affineJacobian e.symm * C)
      (affineImageFamily e F) unitBallBody := by
    simpa only [hambient] using haffine
  apply isFrostmanIn_enlarge_family haffineUnit
  · intro i
    exact himageSubset i
  · intro i
    exact hproxyContained i
  · intro i
    exact affineAxisProxyTube_criticalScale_volume_le_fixed_mul_affineImage
      hradius hradiusHalf t ht a0 b0 c0 d0 (T i) hproxyHalf

end
end Family8Family7CriticalScaleProxyFrostmanTransportV3
