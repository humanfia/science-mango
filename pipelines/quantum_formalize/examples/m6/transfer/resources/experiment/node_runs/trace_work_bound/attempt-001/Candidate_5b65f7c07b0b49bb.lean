import FrozenTarget_5b65f7c07b0b49bb
theorem M6.Transfer.trace_work_bound : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hslots : 2 * N + 1 ≤ 3 * N := by omega
  have hcharge : M6.Transfer.eventBitCharge R N ≤ 60 * N := by
    unfold M6.Transfer.eventBitCharge M6.Transfer.coefficientBits M6.Transfer.addressBits
    omega
  have hpow : ((2 : ℕ)^R)^2 = 4^R := by
    calc
      (2^R)^2 = 2^R * 2^R := by ring
      _ = (2 * 2)^R := (mul_pow (2 : ℕ) 2 R).symm
      _ = 4^R := by norm_num
  have hcount : M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1) ≤ 21 * N^2 * 4^R := by
    rw [M6.Transfer.scatter_loop_count, hpow]
    calc
      6 * N * (2*N+1) * 4^R + 4^R * N * (2*N+1)
          = (7 * N * 4^R) * (2*N+1) := by ring
      _ ≤ (7 * N * 4^R) * (3*N) := Nat.mul_le_mul_left _ hslots
      _ = 21 * N^2 * 4^R := by ring
  unfold M6.Transfer.traceWorkModel
  calc
    (M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1)) * M6.Transfer.eventBitCharge R N
        ≤ (21 * N^2 * 4^R) * (60*N) := Nat.mul_le_mul hcount hcharge
    _ = 1260 * (N^3 * 4^R) := by ring
    _ ≤ 4096 * (N^3 * 4^R) := Nat.mul_le_mul_right _ (by decide : (1260 : ℕ) ≤ 4096)
    _ = 4096 * N^3 * 4^R := by ring
