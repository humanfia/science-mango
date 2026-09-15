import FrozenTarget_db3f5c60808cf3cc
theorem M6.Normalize.divide_degree : QuantumHarnessFrozenTarget := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0
  intro k p n hp d hd
  rw [M6.Normalize.divide_coeff, hp d hd, Int.zero_ediv]
