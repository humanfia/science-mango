import FrozenTarget_5b1dc0d00d041f1a
theorem M6.Normalize.divide_scaled : QuantumHarnessFrozenTarget := by
  change ∀ (k : ℤ) (p : Polynomial ℤ), k ≠ 0 → M6.Normalize.divide k (Polynomial.C k * p) = p
  intro k p hk
  apply Polynomial.ext
  intro d
  rw [M6.Normalize.divide_coeff, Polynomial.coeff_C_mul]
  simp [Int.mul_ediv_cancel_left, hk]
