import Family8Grounding.Family8FiniteENNRealMaxWeightIndexV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8FiniteENNRealMaxWeightFiberV1

open Family8FiniteENNRealMaxWeightIndexV1

noncomputable section

/-- The source fibre whose weight equals the fixed maximal source weight. -/
def maxWeightFiber {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) : Finset alpha :=
  source.filter fun i =>
    weight i = weight (maxWeightIndex source weight hsource)

#print axioms maxWeightFiber

end


end Family8FiniteENNRealMaxWeightFiberV1
