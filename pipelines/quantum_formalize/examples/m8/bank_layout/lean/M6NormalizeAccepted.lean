import M6Normalize

theorem M6.Normalize.divide_coeff : ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k := by
  classical
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k
  intro k p d
  by_cases hd : d ∈ p.support
  · simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd]
  · have hz : p.coeff d = 0 := by simpa using hd
    simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd, hz]

theorem M6.Normalize.scaled_coeff_divisible : ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d
  intro k p d
  rw [Polynomial.coeff_C_mul]
  exact ⟨p.coeff d, rfl⟩

theorem M6.Normalize.divide_degree : ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0 := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0
  intro k p n hp d hd
  rw [M6.Normalize.divide_coeff, hp d hd, Int.zero_ediv]

theorem M6.Normalize.divide_scaled : ∀ (k : ℤ) (p : Polynomial ℤ), k ≠ 0 → M6.Normalize.divide k (Polynomial.C k * p) = p := by
  change ∀ (k : ℤ) (p : Polynomial ℤ), k ≠ 0 → M6.Normalize.divide k (Polynomial.C k * p) = p
  intro k p hk
  apply Polynomial.ext
  intro d
  rw [M6.Normalize.divide_coeff, Polynomial.coeff_C_mul]
  simp [Int.mul_ediv_cancel_left, hk]
#print axioms M6.Normalize.divide_coeff
#print axioms M6.Normalize.divide_degree
#print axioms M6.Normalize.divide_scaled
#print axioms M6.Normalize.scaled_coeff_divisible
