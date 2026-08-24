import Mathlib

set_option autoImplicit false

namespace Family6FiniteMapFiberCapCardV1

universe u v

/-- A finite map with fibers of size at most `cap` loses exactly the
multiplicative factor `cap` when cardinality is transported to its image
container. -/
theorem card_le_fiberCap_mul_card
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (cap : Nat)
    (hmaps : ∀ x ∈ s, f x ∈ t)
    (hcap : ∀ y ∈ t, (s.filter fun x => f x = y).card ≤ cap) :
    s.card ≤ cap * t.card := by
  have hfilter : s.filter (fun x => f x ∈ t) = s :=
    Finset.filter_eq_self.2 hmaps
  calc
    s.card = ∑ y ∈ t, (s.filter fun x => f x = y).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter, hfilter]
    _ ≤ ∑ _y ∈ t, cap := by
      exact Finset.sum_le_sum fun y hy => hcap y hy
    _ = cap * t.card := by
      simp [Nat.mul_comm]

#print axioms card_le_fiberCap_mul_card

end Family6FiniteMapFiberCapCardV1
