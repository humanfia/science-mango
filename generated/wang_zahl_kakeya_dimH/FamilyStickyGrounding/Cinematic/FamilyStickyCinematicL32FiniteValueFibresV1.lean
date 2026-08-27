import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32FiniteValueFibresV1

noncomputable section

universe u v

/-!
# Generic finite value fibres

Lossless finite partitioning by all occupied values, with no sampling or
geometry dependency.
-/

noncomputable def finiteOccupiedValues
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) : Finset value := by
  classical
  exact items.image valueAt

/-- The items in one exact value fibre. -/
noncomputable def finiteValueFiber
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) (c : value) :
    Finset item := by
  classical
  exact items.filter fun a => valueAt a = c

@[simp]
theorem mem_finiteOccupiedValues_iff
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) (c : value) :
    c ∈ finiteOccupiedValues items valueAt <->
      exists a, a ∈ items ∧ valueAt a = c := by
  classical
  simp [finiteOccupiedValues]

@[simp]
theorem mem_finiteValueFiber_iff
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) (c : value)
    (a : item) :
    a ∈ finiteValueFiber items valueAt c <->
      a ∈ items ∧ valueAt a = c := by
  classical
  simp [finiteValueFiber]

theorem finiteValueFiber_nonempty_of_mem
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) {c : value}
    (hc : c ∈ finiteOccupiedValues items valueAt) :
    (finiteValueFiber items valueAt c).Nonempty := by
  rcases (mem_finiteOccupiedValues_iff items valueAt c).mp hc with
    ⟨a, ha, hac⟩
  exact ⟨a, (mem_finiteValueFiber_iff items valueAt c a).mpr ⟨ha, hac⟩⟩

theorem finiteValueFiber_subset
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) (c : value) :
    finiteValueFiber items valueAt c ⊆ items := by
  intro a ha
  exact (mem_finiteValueFiber_iff items valueAt c a).mp ha |>.1

theorem pairwiseDisjoint_finiteValueFiber
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) :
    Set.PairwiseDisjoint
      (finiteOccupiedValues items valueAt : Set value)
      (finiteValueFiber items valueAt) := by
  classical
  intro c _hc d _hd hcd
  change Disjoint (finiteValueFiber items valueAt c)
    (finiteValueFiber items valueAt d)
  rw [Finset.disjoint_left]
  intro a hac had
  have hcEq := (mem_finiteValueFiber_iff items valueAt c a).mp hac |>.2
  have hdEq := (mem_finiteValueFiber_iff items valueAt d a).mp had |>.2
  exact hcd (hcEq.symm.trans hdEq)

theorem biUnion_finiteValueFiber_eq
    {item : Type u} {value : Type v}
    [DecidableEq item]
    (items : Finset item) (valueAt : item -> value) :
    (finiteOccupiedValues items valueAt).biUnion
        (finiteValueFiber items valueAt) = items := by
  classical
  ext a
  simp only [Finset.mem_biUnion, mem_finiteOccupiedValues_iff,
    mem_finiteValueFiber_iff]
  constructor
  · rintro ⟨c, _hc, ha, _hac⟩
    exact ha
  · intro ha
    exact ⟨valueAt a, ⟨a, ha, rfl⟩, ha, rfl⟩

theorem card_eq_sum_finiteValueFiber_card
    {item : Type u} {value : Type v}
    (items : Finset item) (valueAt : item -> value) :
    items.card = ∑ c ∈ finiteOccupiedValues items valueAt,
      (finiteValueFiber items valueAt c).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise fun a ha =>
    (mem_finiteOccupiedValues_iff items valueAt (valueAt a)).mpr
      ⟨a, ha, rfl⟩

#print axioms card_eq_sum_finiteValueFiber_card

end

end FamilyStickyCinematicL32FiniteValueFibresV1
