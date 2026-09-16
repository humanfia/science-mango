import FrozenTarget_6521a030bc1ca16e
theorem M8.AntipodalFamily.modulus_power : QuantumHarnessFrozenTarget := by
  change ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial)^(2^v)
  intro v hv
  simp [M6.Cyclic.modulus, add_pow_char_pow]
