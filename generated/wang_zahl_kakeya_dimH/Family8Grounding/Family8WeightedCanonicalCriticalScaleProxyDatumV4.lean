import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyShadingV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyDatumV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyShadingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

/-- The actual datum on the exact weighted critical-ball proxy family and its
same-object transported shading. `ActualTubeDatum` currently fixes its index
universe to `Type`, so this endpoint deliberately exposes the same universe. -/
def weightedCanonicalCriticalScaleProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real)) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W))
      {i // i ∈ W.criticalBall} where
  family := weightedCanonicalCriticalScaleProxyFamily S W
  shading := weightedCanonicalCriticalScaleProxyShading
    S W Y haxis htransverse

end

end Family8WeightedCanonicalCriticalScaleProxyDatumV4
