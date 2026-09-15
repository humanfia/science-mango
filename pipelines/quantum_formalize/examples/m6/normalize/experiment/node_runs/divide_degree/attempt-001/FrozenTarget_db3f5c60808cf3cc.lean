import M6Normalize

theorem M6.Normalize.divide_coeff : ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k := by
  classical
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k
  intro k p d
  by_cases hd : d ∈ p.support
  · simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd]
  · have hz : p.coeff d = 0 := by simpa using hd
    simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd, hz]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0
