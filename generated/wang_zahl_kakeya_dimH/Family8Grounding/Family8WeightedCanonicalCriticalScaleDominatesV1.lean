import Family8Grounding.Family8WeightedCanonicalCriticalScaleRoundingV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal

namespace Family8WeightedCanonicalCriticalScaleDominatesV1

open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScaleRoundingV1

noncomputable section

universe u

/-- The literal weighted canonical critical choice dominates every real
radius in its full permitted interval. -/
theorem weightedCriticalMaximizer_dominates_on_Icc
    {alpha : Type u} (D : WeightedCanonicalNormBallData alpha)
    {radius : Real} (hradiusLower : D.delta ≤ radius)
    (hradiusUpper : radius ≤ D.ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ D.family) :
    finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
        radius testCenter ≤
      finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
        D.criticalScale D.criticalCenter := by
  obtain ⟨criticalRadius, hcriticalRadius, hscore⟩ :=
    exists_criticalScale_with_weighted_score_ge D.family D.distance D.weight
      testCenter htestCenter (D.self_le_delta testCenter htestCenter)
      D.delta_pos hradiusLower hradiusUpper D.exponent_nonneg
  exact hscore.trans
    (D.weighted_score_dominates_on_criticalCarrier
      hcriticalRadius htestCenter)

end

end Family8WeightedCanonicalCriticalScaleDominatesV1
