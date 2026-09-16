import FrozenTarget_efd411398f646042
theorem M8.FiniteSearch.calls_bound : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), (M8.FiniteSearch.walk test start fuel).2 ≤ fuel
  intro n α test start fuel
  induction fuel generalizing start with
  | zero => simp [M8.FiniteSearch.walk]
  | succ fuel ih =>
      by_cases h : start < n
      · cases ht : test ⟨start, h⟩ with
        | none =>
            simpa [M8.FiniteSearch.walk, h, ht] using
              Nat.add_le_add_right (ih (start + 1)) 1
        | some a =>
            simp [M8.FiniteSearch.walk, h, ht]
      · simp [M8.FiniteSearch.walk, h]
