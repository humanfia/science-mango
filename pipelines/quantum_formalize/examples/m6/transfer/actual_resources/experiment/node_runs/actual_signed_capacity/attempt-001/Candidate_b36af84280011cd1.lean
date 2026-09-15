import FrozenTarget_b36af84280011cd1
theorem M6.Transfer.actual_signed_capacity : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(R + 3*N + 2 - 1)
  intro R N
  have h : R + 3*N + 2 - 1 = R + 3*N + 1 := by omega
  rw [h, pow_add, pow_add, pow_mul]
  norm_num
  have hp : 0 < (2 : ℕ)^R * 8^N := by positivity
  omega
