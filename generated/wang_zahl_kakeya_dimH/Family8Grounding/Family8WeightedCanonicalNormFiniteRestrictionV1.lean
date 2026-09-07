import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Family8WeightedCanonicalNormFiniteRestrictionV1

open Family8Family7NativeHighWeightedCriticalBallV1

noncomputable section

/-- Restrict a weighted canonical norm datum to any nonempty subfamily,
keeping its metric, weights, and scale parameters unchanged. -/
def restrictWeightedNormData {alpha : Type*}
    (D : WeightedCanonicalNormBallData alpha)
    (selected : Finset alpha) (hselected : selected.Nonempty)
    (hsubset : selected ⊆ D.family) :
    WeightedCanonicalNormBallData alpha where
  family := selected
  distance := D.distance
  weight := D.weight
  delta := D.delta
  ceiling := D.ceiling
  exponent := D.exponent
  family_nonempty := hselected
  self_le_delta := fun center hcenter =>
    D.self_le_delta center (hsubset hcenter)
  delta_pos := D.delta_pos
  delta_le_ceiling := D.delta_le_ceiling
  exponent_nonneg := D.exponent_nonneg

end


end Family8WeightedCanonicalNormFiniteRestrictionV1
