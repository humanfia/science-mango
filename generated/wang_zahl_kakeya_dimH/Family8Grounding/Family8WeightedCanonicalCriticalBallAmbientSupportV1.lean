import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set

namespace Family8WeightedCanonicalCriticalBallAmbientSupportV1

open Family8Family7NativeHighWeightedCriticalBallV1

noncomputable section

/-- A weighted canonical critical ball inherits every pointwise support
property of its source family. -/
theorem criticalBall_subset_of_family_subset
    {alpha : Type*} (D : WeightedCanonicalNormBallData alpha)
    (ambient : Set alpha)
    (hfamily : ∀ i, i ∈ D.family → i ∈ ambient) :
    ∀ i, i ∈ D.criticalBall → i ∈ ambient := by
  intro i hi
  exact hfamily i (D.criticalBall_subset_family hi)

end

end Family8WeightedCanonicalCriticalBallAmbientSupportV1
