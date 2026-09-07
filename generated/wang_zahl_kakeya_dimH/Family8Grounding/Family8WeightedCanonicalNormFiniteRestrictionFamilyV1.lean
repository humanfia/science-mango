import Family8Grounding.Family8WeightedCanonicalNormFiniteRestrictionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Family8WeightedCanonicalNormFiniteRestrictionFamilyV1

open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalNormFiniteRestrictionV1

noncomputable section

@[simp] theorem restrictWeightedNormData_family
    {alpha : Type*} (D : WeightedCanonicalNormBallData alpha)
    (selected : Finset alpha) (hselected : selected.Nonempty)
    (hsubset : selected ⊆ D.family) :
    (restrictWeightedNormData D selected hselected hsubset).family = selected :=
  rfl

end

end Family8WeightedCanonicalNormFiniteRestrictionFamilyV1
