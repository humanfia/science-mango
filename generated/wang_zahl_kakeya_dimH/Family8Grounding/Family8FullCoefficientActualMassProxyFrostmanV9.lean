import Family8Grounding.Family8Family7CriticalScaleProxyFrostmanTransportV3
import Family8Grounding.Family8FullCoefficientActualMassProxySupportV10
import Family8Grounding.Family8WeightedCanonicalCriticalBallExactCardFrostmanV1
import Family8Grounding.Family8Family7CriticalScaleProxyVolumeLossV2
import Family8Grounding.Family8ActualRestrictedMassWeightedCriticalBallShadingV4
import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1

/-!
# Frostman transport for the full-coefficient actual-mass proxy

The actual-mass critical ball is restricted using its honest exact cardinal
quotient, then the already-grounded Family7 critical-scale affine transport
is applied to the same ball.  No fixed-cardinality retention or common-c
bucket is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FullCoefficientActualMassProxyFrostmanV9

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7CriticalScaleProxyFrostmanTransportV3
open Family8Family7CriticalScaleProxyVolumeLossV2
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyGeometryV7
open Family8FullCoefficientActualMassProxySupportV10
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8WeightedCanonicalCriticalBallExactCardFrostmanV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section


/-- An explicit Frostman certificate on the whole active family transports
to the literal full-coefficient actual-mass critical-scale proxy. -/
theorem fullCoefficientActualMass_proxyFamily_isFrostmanIn
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hF : IsFrostmanOn C S.family.bodyFamily active unitBallBody) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    IsFrostmanIn
      (criticalScaleAffineProxyVolumeLoss *
        (affineJacobian
            (weightedCanonicalCriticalScaleAffineEquiv S W).symm *
          (C * (16 * weightedCanonicalCriticalBallCardLoss W))))
      (weightedCanonicalCriticalScaleProxyFamily S W).bodyFamily
      unitBallBody := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  obtain ⟨haxis, htransverse, _hchart⟩ :=
    exists_fullCoefficientActualMass_proxyGeometry
      S active hactive hradius htenRadiusSixteen Y X hactiveSource
  obtain ⟨_hproxyFifth, hproxyHalf, hproxyContained⟩ :=
    fullCoefficientActualMass_proxySupport
      S active hactive hradius htenRadiusSixteen Y X hactiveSource
        hcontained
  have hcritical :=
    weightedCanonicalCriticalBall_isFrostmanIn_exactCardLoss
      S.family W unitBallBody (by
        simpa only [W, fullCoefficientActualMassNormData,
          actualRestrictedMassWeightedNormData,
          fullCoefficientNormTemplate] using hF) hradiusHalf
  change IsFrostmanIn
      (C * (16 * weightedCanonicalCriticalBallCardLoss W))
      (fun i : {i // i ∈ W.criticalBall} ↦
        (S.family.tubes i.1).body)
      unitBallBody at hcritical
  have hproxy := criticalScaleAffineProxyFamily_isFrostmanIn
    (T := fun i : {i // i ∈ W.criticalBall} ↦ S.family.tubes i.1)
    (hradius := hradius) (hradiusHalf := hradiusHalf)
    W.criticalScale (weightedCanonicalCriticalScale_pos W)
    (projectedTubeGraphA (S.family.tubes W.criticalCenter))
    (projectedTubeGraphB (S.family.tubes W.criticalCenter))
    (projectedTubeGraphC (S.family.tubes W.criticalCenter))
    (projectedTubeGraphD (S.family.tubes W.criticalCenter))
    hproxyHalf haxis htransverse hproxyContained hcritical
  change IsFrostmanIn
    (criticalScaleAffineProxyVolumeLoss *
      (affineJacobian
          (weightedCanonicalCriticalScaleAffineEquiv S W).symm *
        (C * (16 * weightedCanonicalCriticalBallCardLoss W))))
    (fun i : {i // i ∈ W.criticalBall} ↦
      (affineAxisProxyTube
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W))
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)).body)
    unitBallBody
  exact hproxy

#print axioms fullCoefficientActualMass_proxyFamily_isFrostmanIn

end
end Family8FullCoefficientActualMassProxyFrostmanV9
