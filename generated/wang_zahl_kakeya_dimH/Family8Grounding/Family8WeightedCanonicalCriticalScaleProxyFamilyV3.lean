import Family8Grounding.Family8WeightedCanonicalCriticalScaleAffineEquivV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyFamilyV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Genuine round-tube proxy family on the literal critical-ball subtype of
an arbitrary weighted canonical datum. -/
def weightedCanonicalCriticalScaleProxyFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota) :
    UniformTubeFamily
      (criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W))
      {i // i ∈ W.criticalBall} where
  tubes i := affineAxisProxyTube
    (criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W))
    (weightedCanonicalCriticalScaleAffineEquiv S W)
    (S.family.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

end

end Family8WeightedCanonicalCriticalScaleProxyFamilyV3
