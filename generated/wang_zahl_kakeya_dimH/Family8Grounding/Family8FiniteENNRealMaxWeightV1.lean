import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8FiniteENNRealMaxWeightV1

noncomputable section

/-- A nonempty finite family has a member of maximal `ENNReal` weight. -/
theorem exists_max_weight {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) :
    ∃ i, i ∈ source ∧ ∀ j, j ∈ source → weight j ≤ weight i := by
  exact Finset.exists_max_image source weight hsource

#print axioms exists_max_weight

end


end Family8FiniteENNRealMaxWeightV1
