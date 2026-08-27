import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteValueFibresWeightedV1

open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Weighted finite value fibres

An exact finite value partition is lossless for arbitrary `ENNReal` weights.
This is the mass analogue of `card_eq_sum_finiteValueFiber_card`; it does not
assume that any weight is finite.
-/

/-- The total extended-real weight is the sum of the weights of all occupied
exact-value fibres. -/
theorem finiteENNRealWeight_eq_sum_finiteValueFiberWeight
    {item : Type u} {value : Type v} [DecidableEq item]
    (items : Finset item) (valueAt : item -> value)
    (weight : item -> ENNReal) :
    finiteENNRealWeight items weight =
      ∑ c ∈ finiteOccupiedValues items valueAt,
        ∑ a ∈ finiteValueFiber items valueAt c, weight a := by
  classical
  rw [finiteENNRealWeight]
  have hmaps : (items : Set item).MapsTo valueAt
      (finiteOccupiedValues items valueAt : Set value) := by
    intro a ha
    exact (mem_finiteOccupiedValues_iff items valueAt (valueAt a)).2
      ⟨a, ha, rfl⟩
  simpa only [finiteOccupiedValues, finiteValueFiber] using
    (Finset.sum_fiberwise_of_maps_to hmaps weight).symm

#print axioms finiteENNRealWeight_eq_sum_finiteValueFiberWeight

end

end FamilyStickyCinematicL32FiniteValueFibresWeightedV1
