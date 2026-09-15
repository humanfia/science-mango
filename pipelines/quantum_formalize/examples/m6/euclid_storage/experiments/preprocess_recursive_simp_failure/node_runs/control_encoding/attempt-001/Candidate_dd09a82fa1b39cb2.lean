import FrozenTarget_dd09a82fa1b39cb2
theorem M6.EuclidStorage.control_encoding : QuantumHarnessFrozenTarget := by
  change ∀ (width v : ℕ), v ≤ 32 * width → v < 2 ^ (M6.EuclidStorage.registerBits width)
  intro width v hv
  have h : width < 2 ^ width := Nat.lt_two_pow_self
  change v < 2 ^ (width + 5)
  rw [pow_add]
  norm_num
  omega
