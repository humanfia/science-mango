import FrozenTarget_c429ad3f1e062d02
theorem M5.Signature.divisor_constant_one : QuantumHarnessFrozenTarget := by
  change ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1
  intro P a hdiv ha
  obtain ⟨q, rfl⟩ := hdiv
  rw [Polynomial.mul_coeff_zero] at ha
  have h : ∀ c d : ZMod 2, c * d = 1 → c = 1 := by decide
  exact h (P.coeff 0) (q.coeff 0) ha
