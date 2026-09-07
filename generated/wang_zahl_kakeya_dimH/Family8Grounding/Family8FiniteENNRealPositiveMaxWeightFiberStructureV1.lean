import Mathlib.Data.ENNReal.BigOperators
import Family8Grounding.Family8FiniteENNRealMaxWeightFiberV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace Family8FiniteENNRealPositiveMaxWeightFiberStructureV1

open Family8FiniteENNRealMaxWeightFiberV1
open Family8FiniteENNRealMaxWeightIndexV1

noncomputable section

/-- A positive exact maximal-weight fibre with its full cardinality-loss
retention package. -/
structure PositiveMaxWeightFiberData {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) where
  value_ne_zero : weight (maxWeightIndex source weight hsource) ≠ 0
  fiber_nonempty : (maxWeightFiber source weight hsource).Nonempty
  fiber_subset : maxWeightFiber source weight hsource ⊆ source
  common_weight : ∀ i ∈ maxWeightFiber source weight hsource,
    weight i = weight (maxWeightIndex source weight hsource)
  totalWeight_le :
    (∑ i ∈ source, weight i) ≤
      (source.card : ENNReal) *
        ∑ i ∈ maxWeightFiber source weight hsource, weight i

#print axioms PositiveMaxWeightFiberData

end


end Family8FiniteENNRealPositiveMaxWeightFiberStructureV1
