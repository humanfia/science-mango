import Family8Grounding.Family8WeightedCanonicalCriticalScalePositiveV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleAffineMapV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleAffineEquivV1

open LeanEval.Analysis.WangZahlKakeya
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Critical-scale affine normalization for an arbitrary weighted canonical
datum on an actual uniform source. -/
def weightedCanonicalCriticalScaleAffineEquiv
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota) :
    Space ≃ᵃ[Real] Space :=
  let T0 := S.family.tubes W.criticalCenter
  criticalScaleAffineEquiv W.criticalScale
    (weightedCanonicalCriticalScale_pos W)
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)

end

end Family8WeightedCanonicalCriticalScaleAffineEquivV1
