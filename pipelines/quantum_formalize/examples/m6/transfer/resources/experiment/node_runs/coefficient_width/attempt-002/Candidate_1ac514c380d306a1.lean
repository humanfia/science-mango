import FrozenTarget_1ac514c380d306a1
theorem M6.Transfer.coefficient_width : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(R + 3*N + 2)
  intro R N
  have h : 0 < (2 : ℕ)^R * 8^N := by positivity
  norm_num [pow_add, pow_mul] <;> nlinarith
