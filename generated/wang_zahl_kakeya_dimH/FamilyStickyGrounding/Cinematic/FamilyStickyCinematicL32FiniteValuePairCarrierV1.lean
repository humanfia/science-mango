import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32FiniteValuePairCarrierV1

open FamilyStickyCinematicL32FiniteValueFibresV1

noncomputable section

universe u v w

/-!
# Deduplicated endpoint carriers over finite value fibres

This package-free module separates the item partition from the possibly
non-injective endpoint maps.  If both endpoint maps carry the item's value,
then the deduplicated endpoint carriers of distinct values are disjoint.
-/

/-- Deduplicated union of two endpoint maps on a finite item family. -/
def finitePairCarrier
    {item : Type u} {curve : Type v}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (T U : item -> curve) : Finset curve :=
  items.image T ∪ items.image U

/-- Deduplicated endpoints belonging to one exact value fibre. -/
noncomputable def finiteValuePairCarrierAt
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) (c : value) : Finset curve :=
  finitePairCarrier (finiteValueFiber items valueAt c) T U

theorem curveValue_eq_of_mem_finiteValuePairCarrierAt
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) (curveValue : curve -> value)
    (hT : forall a, a ∈ items -> curveValue (T a) = valueAt a)
    (hU : forall a, a ∈ items -> curveValue (U a) = valueAt a)
    (c : value) {V : curve}
    (hV : V ∈ finiteValuePairCarrierAt items valueAt T U c) :
    curveValue V = c := by
  classical
  simp only [finiteValuePairCarrierAt, finitePairCarrier,
    Finset.mem_union, Finset.mem_image] at hV
  rcases hV with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · have haData := (mem_finiteValueFiber_iff items valueAt c a).mp ha
    exact (hT a haData.1).trans haData.2
  · have haData := (mem_finiteValueFiber_iff items valueAt c a).mp ha
    exact (hU a haData.1).trans haData.2

theorem finiteValuePairCarrierAt_subset_global
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) (c : value) :
    finiteValuePairCarrierAt items valueAt T U c ⊆
      finitePairCarrier items T U := by
  classical
  intro V hV
  simp only [finiteValuePairCarrierAt, finitePairCarrier,
    Finset.mem_union, Finset.mem_image] at hV ⊢
  rcases hV with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, finiteValueFiber_subset items valueAt c ha, rfl⟩
  · exact Or.inr ⟨a, finiteValueFiber_subset items valueAt c ha, rfl⟩

theorem pairwiseDisjoint_finiteValuePairCarrierAt
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) (curveValue : curve -> value)
    (hT : forall a, a ∈ items -> curveValue (T a) = valueAt a)
    (hU : forall a, a ∈ items -> curveValue (U a) = valueAt a) :
    Set.PairwiseDisjoint
      (finiteOccupiedValues items valueAt : Set value)
      (finiteValuePairCarrierAt items valueAt T U) := by
  classical
  intro c _hc d _hd hcd
  change Disjoint (finiteValuePairCarrierAt items valueAt T U c)
    (finiteValuePairCarrierAt items valueAt T U d)
  rw [Finset.disjoint_left]
  intro V hVc hVd
  have hcEq := curveValue_eq_of_mem_finiteValuePairCarrierAt
    items valueAt T U curveValue hT hU c hVc
  have hdEq := curveValue_eq_of_mem_finiteValuePairCarrierAt
    items valueAt T U curveValue hT hU d hVd
  exact hcd (hcEq.symm.trans hdEq)

theorem biUnion_finiteValuePairCarrierAt_eq_global
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) :
    (finiteOccupiedValues items valueAt).biUnion
        (finiteValuePairCarrierAt items valueAt T U) =
      finitePairCarrier items T U := by
  classical
  ext V
  simp only [Finset.mem_biUnion, mem_finiteOccupiedValues_iff,
    finiteValuePairCarrierAt, finitePairCarrier, Finset.mem_union,
    Finset.mem_image, mem_finiteValueFiber_iff]
  constructor
  · rintro ⟨c, _hc, ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩⟩
    · exact Or.inl ⟨a, ha.1, rfl⟩
    · exact Or.inr ⟨a, ha.1, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨valueAt a, ⟨a, ha, rfl⟩,
        Or.inl ⟨a, ⟨ha, rfl⟩, rfl⟩⟩
    · exact ⟨valueAt a, ⟨a, ha, rfl⟩,
        Or.inr ⟨a, ⟨ha, rfl⟩, rfl⟩⟩

theorem finitePairCarrier_card_eq_sum_valueFiber_card
    {item : Type u} {curve : Type v} {value : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (valueAt : item -> value)
    (T U : item -> curve) (curveValue : curve -> value)
    (hT : forall a, a ∈ items -> curveValue (T a) = valueAt a)
    (hU : forall a, a ∈ items -> curveValue (U a) = valueAt a) :
    (finitePairCarrier items T U).card =
      ∑ c ∈ finiteOccupiedValues items valueAt,
        (finiteValuePairCarrierAt items valueAt T U c).card := by
  classical
  rw [← Finset.card_biUnion
    (pairwiseDisjoint_finiteValuePairCarrierAt
      items valueAt T U curveValue hT hU)]
  exact congrArg Finset.card
    (biUnion_finiteValuePairCarrierAt_eq_global items valueAt T U).symm

#print axioms pairwiseDisjoint_finiteValuePairCarrierAt
#print axioms biUnion_finiteValuePairCarrierAt_eq_global
#print axioms finitePairCarrier_card_eq_sum_valueFiber_card

end

end FamilyStickyCinematicL32FiniteValuePairCarrierV1
