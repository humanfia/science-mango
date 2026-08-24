import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41CyclicSortedTripleOrderV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1

/-
# A sorted cyclic triple gives a scalar cyclic order

This is a list-theoretic bridge.  If a representative cyclic sequence is
strictly sorted, then a positively oriented triple has one of the three
corresponding strict scalar orders.  No geometric ordering is assumed.
-/

theorem cyc3_of_cyclicallyOrdered_of_pairwise_lt
    {alpha : Type*} [DecidableEq alpha] [LinearOrder alpha]
    (A : DistinctCyclicSequence alpha) (x y z : alpha)
    (hsorted : A.order.Pairwise (fun a b => a < b))
    (hcyclic : CyclicallyOrdered A x y z) :
    (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y) := by
  have htriple : (tripleOrder A x y z).Pairwise (fun a b => a < b) :=
    hsorted.filter _
  rcases hcyclic.symm with ⟨n, hn⟩
  have hnmod : [x, y, z].rotate (n % 3) = tripleOrder A x y z := by
    calc
      [x, y, z].rotate (n % 3) = [x, y, z].rotate n :=
        List.rotate_mod [x, y, z] n
      _ = tripleOrder A x y z := hn
  rw [← hnmod] at htriple
  have hrem : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · simp [hzero] at htriple
    exact Or.inl ⟨htriple.1.1, htriple.2⟩
  · simp [hone] at htriple
    exact Or.inr (Or.inl ⟨htriple.1.1, htriple.2⟩)
  · simp [htwo] at htriple
    exact Or.inr (Or.inr ⟨htriple.1.1, htriple.2⟩)

#print axioms cyc3_of_cyclicallyOrdered_of_pairwise_lt

end FamilyStickyCinematicL32Prop41CyclicSortedTripleOrderV1
