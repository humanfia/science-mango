import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Family8WeightedCanonicalCriticalBallIndexCardV1

open Family8Family7NativeHighWeightedCriticalBallV1

noncomputable section

/-- The literal critical-ball subtype never has more indices than its source
family.  This is the cardinal input needed by the generic greedy/Frostman
handoff after a local finite restriction. -/
theorem weightedCanonicalCriticalBallIndex_card_le_family_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (D : WeightedCanonicalNormBallData alpha) :
    Fintype.card {i // i ∈ D.criticalBall} ≤ D.family.card := by
  rw [Fintype.card_coe]
  exact Finset.card_le_card D.criticalBall_subset_family

end

end Family8WeightedCanonicalCriticalBallIndexCardV1
