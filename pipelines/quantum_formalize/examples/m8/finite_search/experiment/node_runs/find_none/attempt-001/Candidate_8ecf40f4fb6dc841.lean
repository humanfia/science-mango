import FrozenTarget_8ecf40f4fb6dc841
theorem M8.FiniteSearch.find_none : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.walk test 0 n).1 = none ↔ ∀ i, test i = none
  intro n α test
  rw [M8.FiniteSearch.none_iff n α test 0 n]
  constructor
  · intro h i
    exact h i (Nat.zero_le _) (by simpa using i.isLt)
  · intro h i _ _
    exact h i
