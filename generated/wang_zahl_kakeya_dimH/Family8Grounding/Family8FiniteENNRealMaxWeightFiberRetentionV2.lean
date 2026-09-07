import Mathlib.Data.ENNReal.BigOperators
import Family8Grounding.Family8FiniteENNRealMaxWeightFiberV1
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexMemV1
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexDominatesV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace Family8FiniteENNRealMaxWeightFiberRetentionV2

open Family8FiniteENNRealMaxWeightFiberV1
open Family8FiniteENNRealMaxWeightIndexV1
open Family8FiniteENNRealMaxWeightIndexMemV1
open Family8FiniteENNRealMaxWeightIndexDominatesV1

noncomputable section

/-- The exact fibre of the maximal source weight retains total weight with at
most the source-cardinality loss. -/
theorem totalWeight_le_card_mul_maxWeightFiberWeight
    {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty) :
    (∑ i ∈ source, weight i) ≤
      (source.card : ENNReal) *
        ∑ i ∈ maxWeightFiber source weight hsource, weight i := by
  have hmaxMem :
      maxWeightIndex source weight hsource ∈
        maxWeightFiber source weight hsource := by
    rw [maxWeightFiber, Finset.mem_filter]
    exact ⟨maxWeightIndex_mem source weight hsource, rfl⟩
  have hmaxLe :
      weight (maxWeightIndex source weight hsource) ≤
        ∑ i ∈ maxWeightFiber source weight hsource, weight i :=
    Finset.single_le_sum
      (fun _ _ => show (0 : ENNReal) ≤ _ from bot_le) hmaxMem
  calc
    (∑ i ∈ source, weight i) ≤
        source.card •
          (∑ i ∈ maxWeightFiber source weight hsource, weight i) :=
      Finset.sum_le_card_nsmul source weight
        (∑ i ∈ maxWeightFiber source weight hsource, weight i)
        (fun i hi =>
          (weight_le_maxWeightIndex source weight hsource hi).trans hmaxLe)
    _ = (source.card : ENNReal) *
          ∑ i ∈ maxWeightFiber source weight hsource, weight i := by
      simp only [nsmul_eq_mul]

#print axioms totalWeight_le_card_mul_maxWeightFiberWeight

end


end Family8FiniteENNRealMaxWeightFiberRetentionV2
