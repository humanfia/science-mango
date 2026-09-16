import FrozenTarget_53e5bbf3585460f5
theorem M8.WeightedSearch.zero_cost : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), (∀ i, (test i).2 = 0) → (M8.WeightedSearch.walk test start fuel).work = 0
  intro n α test start fuel hzero
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : start < n
      · cases hq : (test ⟨start, h⟩).1 <;>
          simp [M8.WeightedSearch.walk, h, hq, hzero, ih]
      · simp [M8.WeightedSearch.walk, h]
