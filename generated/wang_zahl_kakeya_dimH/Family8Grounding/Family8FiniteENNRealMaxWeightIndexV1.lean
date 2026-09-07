import Family8Grounding.Family8FiniteENNRealMaxWeightV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8FiniteENNRealMaxWeightIndexV1

open Family8FiniteENNRealMaxWeightV1

noncomputable section

/-- A fixed maximal-weight member of a nonempty finite family. -/
noncomputable def maxWeightIndex {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) : alpha :=
  Classical.choose (exists_max_weight source weight hsource)

#print axioms maxWeightIndex

end


end Family8FiniteENNRealMaxWeightIndexV1
