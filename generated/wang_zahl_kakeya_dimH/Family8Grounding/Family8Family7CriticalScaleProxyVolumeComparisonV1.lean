import Family8Grounding.Family8Family7CriticalScaleProxyVolumeLossV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7CriticalScaleProxyVolumeComparisonV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffineConvexVolumeCoreV1
open Family8Family7CriticalScaleProxyVolumeLossV2
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFineProxyKatzTaoV3

noncomputable section

/-! The exact affine image is enlarged to the round proxy at fixed cost. -/

theorem affineAxisProxyTube_criticalScale_volume_le_fixed_mul_affineImage
    {radius : NNReal} (hradius : 0 < radius)
    (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real)
    (T : Tube radius)
    (hproxyHalf : criticalScaleProxyRadius radius t ht ≤ (2 : NNReal)⁻¹) :
    volume
        (affineAxisProxyTube (criticalScaleProxyRadius radius t ht)
          (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T).carrier ≤
      criticalScaleAffineProxyVolumeLoss *
        volume
          (affineImageConvexBody
            (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T.body : Set Space) := by
  let e := criticalScaleAffineEquiv t ht a0 b0 c0 d0
  let s := criticalScaleProxyRadius radius t ht
  have hvolume := affineAxisProxyTube_volume_le_ratio_mul_source
    e T hradius hradiusHalf hproxyHalf
  calc
    volume (affineAxisProxyTube s e T).carrier ≤
        affineAxisProxyVolumeRatio radius s * volume T.carrier := hvolume
    _ = (criticalScaleAffineProxyVolumeLoss * affineJacobian e) *
          volume T.carrier := by
      rw [affineAxisProxyVolumeRatio_criticalScale_eq_loss_mul_jacobian
        radius hradius t ht a0 b0 c0 d0]
    _ = criticalScaleAffineProxyVolumeLoss *
          (affineJacobian e * volume T.carrier) := by ac_rfl
    _ = criticalScaleAffineProxyVolumeLoss *
        volume (affineImageConvexBody e T.body : Set Space) := by
      rw [volume_affineImageConvexBody]
      rfl

#print axioms
  affineAxisProxyTube_criticalScale_volume_le_fixed_mul_affineImage

end
end Family8Family7CriticalScaleProxyVolumeComparisonV1
