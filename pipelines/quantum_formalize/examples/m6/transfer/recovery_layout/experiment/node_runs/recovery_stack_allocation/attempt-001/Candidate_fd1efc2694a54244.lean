import FrozenTarget_fd1efc2694a54244
theorem M6.Transfer.recovery_stack_allocation : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, _
  intro R N
  by_cases h : N < 3
  · interval_cases N <;>
      simp [M6.Transfer.pairedQueryStorage, M6.Transfer.recoveryStackBits,
        M6.Transfer.queryCoefficientBits, M6.Transfer.actualAddressBits,
        M6.Transfer.coefficientBits, List.length_finRange] <;>
      ring_nf <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = k + 3 := ⟨N - 3, by omega⟩
    simp [M6.Transfer.pairedQueryStorage, M6.Transfer.recoveryStackBits,
      M6.Transfer.queryCoefficientBits, M6.Transfer.actualAddressBits,
      M6.Transfer.coefficientBits, List.length_finRange]
    ring_nf
    omega
