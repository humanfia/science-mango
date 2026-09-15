import M5Binomial

theorem M5.Binomial.negative_coeff : ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ) := by
  change ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ)
  intro m j
  have h : (1 : Polynomial ℤ) - Polynomial.X =
      Polynomial.X * Polynomial.C (-1 : ℤ) + 1 := by
    simp
    <;> ring
  rw [h, add_pow, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, one_pow, mul_one, mul_pow,
    ← Polynomial.C_pow, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Polynomial.coeff_X_pow, hij, hij.symm]
  · intro hj
    have hmj : m < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hmj]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k-j) : ℤ)
