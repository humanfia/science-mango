import FrozenTarget_1db4610b4ec2e597
theorem M5.Binomial.binomial_convolution : QuantumHarnessFrozenTarget := by
  change ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k - j) : ℤ)
  intro m n k
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [M5.Binomial.negative_coeff, Polynomial.coeff_one_add_X_pow]
