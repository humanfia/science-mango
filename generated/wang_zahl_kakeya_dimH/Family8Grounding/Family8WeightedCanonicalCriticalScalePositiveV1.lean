import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Family8WeightedCanonicalCriticalScalePositiveV1

open Family8Family7NativeHighWeightedCriticalBallV1

noncomputable section

theorem weightedCanonicalCriticalScale_pos
    {alpha : Type*} (D : WeightedCanonicalNormBallData alpha) :
    0 < D.criticalScale :=
  D.delta_pos.trans_le D.criticalScale_bounds.1

end

end Family8WeightedCanonicalCriticalScalePositiveV1
