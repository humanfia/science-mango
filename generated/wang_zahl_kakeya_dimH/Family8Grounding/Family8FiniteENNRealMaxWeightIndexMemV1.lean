import Family8Grounding.Family8FiniteENNRealMaxWeightIndexV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8FiniteENNRealMaxWeightIndexMemV1

open Family8FiniteENNRealMaxWeightV1
open Family8FiniteENNRealMaxWeightIndexV1

noncomputable section

/-- The fixed maximal-weight index lies in its source family. -/
theorem maxWeightIndex_mem {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) :
    maxWeightIndex source weight hsource ∈ source :=
  (Classical.choose_spec (exists_max_weight source weight hsource)).1

#print axioms maxWeightIndex_mem

end


end Family8FiniteENNRealMaxWeightIndexMemV1
