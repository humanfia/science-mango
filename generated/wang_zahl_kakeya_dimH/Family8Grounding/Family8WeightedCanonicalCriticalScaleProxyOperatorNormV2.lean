import Family8Grounding.Family8WeightedCanonicalCriticalScaleAffineEquivV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyOperatorNormV2

open LeanEval.Analysis.WangZahlKakeya
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleOperatorNormV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The linear norm of the weighted critical-scale normalization is controlled
by the inverse critical scale. -/
theorem weightedCanonicalCriticalScaleProxy_operatorNorm_le_two_div
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (hcenterSource : W.criticalCenter ∈ S.source)
    (hceiling : W.ceiling ≤ 16) :
    affineLinearOperatorNorm
        (weightedCanonicalCriticalScaleAffineEquiv S W) ≤
      2 / W.criticalScale := by
  let t := W.criticalScale
  let T0 := S.family.tubes W.criticalCenter
  have ht : 0 < t := weightedCanonicalCriticalScale_pos W
  have hrefForwardHalf : (1 / 2 : Real) ≤ |T0.axis.direction 2| := by
    apply S.source_direction_final_half W.criticalCenter
    exact hcenterSource
  have hc0 : |projectedTubeGraphC T0| ≤ 2 :=
    abs_projectedTubeGraphC_le_two_of_abs_final_half T0 hrefForwardHalf
  have hd0 : |projectedTubeGraphD T0| ≤ 2 :=
    abs_projectedTubeGraphD_le_two_of_abs_final_half T0 hrefForwardHalf
  have hscaleUpper : t ≤ 16 :=
    W.criticalScale_bounds.2.trans hceiling
  change affineLinearOperatorNorm
    (criticalScaleAffineEquiv t ht
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)) ≤ 2 / t
  exact affineLinearOperatorNorm_criticalScaleAffineEquiv_le_two_div
    t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)
    hscaleUpper hc0 hd0

end

end Family8WeightedCanonicalCriticalScaleProxyOperatorNormV2
