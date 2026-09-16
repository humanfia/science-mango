import FrozenTarget_a5a239cf52aafeac
theorem M8.WeightedSearch.find_projection : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ), _
  intro n α test
  simpa only [M8.WeightedSearch.find, M8.FiniteSearch.find] using
    M8.WeightedSearch.projection n α test 0 n
