import FrozenTarget_32ff8fd02faefa29
theorem M6.Euclid.dense_cancel : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (p q : M6.Euclid.BP), p ≠ 0 → _
  intro N p q hp
  have hl : p.leadingCoeff = 1 := (M6.Euclid.binary_normalization p).1 hp
  have hsub : ∀ a b : ZMod 2, a - b = a + b := by decide
  have hc : M6.Euclid.cancel p q = p - q * Polynomial.X ^ (p.natDegree - q.natDegree) := by
    simp [M6.Euclid.cancel, hl, mul_comm, mul_left_comm, mul_assoc]
  rw [hc]
  unfold M6.Euclid.dense M6.Euclid.denseXor
  congr 1
  funext i
  simp [Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', hsub]
