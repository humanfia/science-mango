import FrozenTarget_8662d248736f0ede
theorem M8.FiniteSearch.find_bound : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).2 ≤ n
  intro n α test
  exact M8.FiniteSearch.calls_bound n α test 0 n
