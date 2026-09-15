import FrozenTarget_7940b3fd22c758a1
theorem M6.Transfer.coefficient_width : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(R + 3*N + 2)
  intro R N
  rw [pow_add, pow_add, pow_mul]
  norm_num
  have h : 0 < (2 : ℕ)^R * 8^N := by positivity
  nlinarith
