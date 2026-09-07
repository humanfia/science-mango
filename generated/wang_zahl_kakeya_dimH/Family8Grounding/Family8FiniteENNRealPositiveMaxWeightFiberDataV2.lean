import Family8Grounding.Family8FiniteENNRealPositiveMaxWeightFiberStructureV1
import Family8Grounding.Family8FiniteENNRealMaxWeightFiberRetentionV2
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexMemV1
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexDominatesV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace Family8FiniteENNRealPositiveMaxWeightFiberDataV2

open Family8FiniteENNRealMaxWeightFiberV1
open Family8FiniteENNRealMaxWeightFiberRetentionV2
open Family8FiniteENNRealMaxWeightIndexV1
open Family8FiniteENNRealMaxWeightIndexMemV1
open Family8FiniteENNRealMaxWeightIndexDominatesV1
open Family8FiniteENNRealPositiveMaxWeightFiberStructureV1

noncomputable section

/-- Produce the positive exact maximal-weight fibre from nonzero total
weight. -/
theorem positiveMaxWeightFiberData
    {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha → ENNReal)
    (hsource : source.Nonempty)
    (htotal : (∑ i ∈ source, weight i) ≠ 0) :
    PositiveMaxWeightFiberData source weight hsource := by
  have hvalue : weight (maxWeightIndex source weight hsource) ≠ 0 := by
    intro hzero
    apply htotal
    apply Finset.sum_eq_zero
    intro i hi
    have hle := weight_le_maxWeightIndex source weight hsource hi
    rw [hzero] at hle
    exact bot_unique hle
  have hmaxMem :
      maxWeightIndex source weight hsource ∈
        maxWeightFiber source weight hsource := by
    rw [maxWeightFiber, Finset.mem_filter]
    exact ⟨maxWeightIndex_mem source weight hsource, rfl⟩
  exact
    { value_ne_zero := hvalue
      fiber_nonempty := ⟨maxWeightIndex source weight hsource, hmaxMem⟩
      fiber_subset := Finset.filter_subset _ _
      common_weight := fun _ hi => (Finset.mem_filter.mp hi).2
      totalWeight_le :=
        totalWeight_le_card_mul_maxWeightFiberWeight source weight hsource }

#print axioms positiveMaxWeightFiberData

end


end Family8FiniteENNRealPositiveMaxWeightFiberDataV2
