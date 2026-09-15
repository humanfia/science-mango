import FrozenTarget_1c1fde32d767e667
theorem M6.Transfer.actual_address_capacity : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N)
  intro R N hRN
  have hpow : ∀ n : ℕ, n ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ)^n := by positivity
      omega
  have hsq : N^2 ≤ ((2 : ℕ)^N)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hpow N) (hpow N)
  have heq : (2 : ℕ)^(R + 2*N + 12) = 4096 * (2^N)^2 * 2^R := by
    rw [show R + 2*N + 12 = R + N*2 + 12 by omega]
    simp only [pow_add, pow_mul]
    norm_num
    <;> ring
  calc
    M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R :=
      M6.Transfer.actual_trace_storage_bound R N hRN
    _ ≤ 4096 * (2^N)^2 * 2^R :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4096 hsq)
    _ = 2^(R + 2*N + 12) := heq.symm
    _ < 2^(M6.Transfer.actualAddressBits R N) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
      unfold M6.Transfer.actualAddressBits
      omega
