import FrozenTarget_f2f69db3bc8d28ee
theorem M6.Normalize.scaled_coeff_divisible : QuantumHarnessFrozenTarget := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d
  intro k p d
  rw [Polynomial.coeff_C_mul]
  exact ⟨p.coeff d, rfl⟩
