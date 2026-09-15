import FrozenTarget_169502af65632c27
theorem M6.EuclidStorage.control_encoding : QuantumHarnessFrozenTarget := by
  change ∀ (width v : ℕ), v ≤ 32 * width → v < 2 ^ (M6.EuclidStorage.registerBits width)
  intro width v hv
  change v < 2 ^ (width + 5)
  rw [pow_add]
  norm_num
  have h := Nat.lt_two_pow_self width
  omega
