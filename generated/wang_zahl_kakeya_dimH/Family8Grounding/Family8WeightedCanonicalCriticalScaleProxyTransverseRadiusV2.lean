import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyOperatorNormV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2

open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyOperatorNormV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The weighted critical-scale affine image has the literal normalized
transverse radius. -/
theorem weightedCanonicalCriticalScaleProxy_transverseRadius
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (hcenterSource : W.criticalCenter ∈ S.source)
    (hceiling : W.ceiling ≤ 16) :
    affineLinearOperatorNorm
        (weightedCanonicalCriticalScaleAffineEquiv S W) * (radius : Real) ≤
      (criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : Real) := by
  rw [criticalScaleProxyRadius_coe]
  calc
    affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) * (radius : Real) ≤
        (2 / W.criticalScale) * (radius : Real) :=
      mul_le_mul_of_nonneg_right
        (weightedCanonicalCriticalScaleProxy_operatorNorm_le_two_div
          S W hcenterSource hceiling)
        (by positivity)
    _ = 2 * (radius : Real) / W.criticalScale := by ring

end

end Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2
