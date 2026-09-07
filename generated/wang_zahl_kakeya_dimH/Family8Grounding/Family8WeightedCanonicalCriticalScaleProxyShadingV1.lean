import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyFamilyV3
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyShadingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Transport a source shading to the literal weighted critical-scale proxy
family, using only the separately proved longitudinal and transverse facts. -/
def weightedCanonicalCriticalScaleProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
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
    Shading (weightedCanonicalCriticalScaleProxyFamily S W).bodyFamily where
  carrier i := weightedCanonicalCriticalScaleAffineEquiv S W ''
    Y.carrier i.1
  measurable_carrier i :=
    (weightedCanonicalCriticalScaleAffineEquiv
      S W).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1) (haxis i) htransverse)

end

end Family8WeightedCanonicalCriticalScaleProxyShadingV1
