import M6TransferResources

theorem M6.Transfer.state_count : ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R := by
  change ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2 ^ R
  intro R
  simp [M6.Transfer.Memory, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]

theorem M6.Transfer.scatter_loop_count : ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2*N+1) * 4^R := by
  change ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2 * N + 1) * 4 ^ R
  intro R N
  simp only [M6.Transfer.traceCoefficientOps, M6.Transfer.ScatterEvent,
    Fintype.card_prod, M6.Transfer.state_count, Fintype.card_fin,
    M6.Transfer.Bit, ZMod.card]
  have hpow : (4 : ℕ) ^ R = 2 ^ R * 2 ^ R := by
    simpa using (mul_pow (2 : ℕ) 2 R)
  rw [hpow]
  ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R
