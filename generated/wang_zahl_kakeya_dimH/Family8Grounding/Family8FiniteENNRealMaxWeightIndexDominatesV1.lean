import Family8Grounding.Family8FiniteENNRealMaxWeightIndexV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8FiniteENNRealMaxWeightIndexDominatesV1

open Family8FiniteENNRealMaxWeightV1
open Family8FiniteENNRealMaxWeightIndexV1

noncomputable section

/-- Every source weight is bounded by the fixed maximal weight. -/
theorem weight_le_maxWeightIndex {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) {i : alpha} (hi : i ∈ source) :
    weight i ≤ weight (maxWeightIndex source weight hsource) :=
  (Classical.choose_spec (exists_max_weight source weight hsource)).2 i hi

#print axioms weight_le_maxWeightIndex

end


end Family8FiniteENNRealMaxWeightIndexDominatesV1
