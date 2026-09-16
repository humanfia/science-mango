import FrozenTarget_4a5989a0568c3457
theorem M8.BankLayout.workspace_monotone : QuantumHarnessFrozenTarget := by
  change ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots
  intro R S N slots hRS
  have hp : 2 ^ R ≤ (2 : ℕ) ^ S := pow_le_pow_right₀ (by decide) hRS
  have hlen (r : ℕ) : (M6.Transfer.scatterEventList r N).length = 2 ^ r * 2 * (2 * N + 1) * 3 := by
    classical
    simp [M6.Transfer.scatterEventList, M6.Transfer.ScatterEvent,
      M6.Transfer.Bit, M6.Transfer.state_count, Fintype.card_prod, mul_assoc]
  simp only [M6.Transfer.solveStorage, M6.Transfer.pairedQueryStorage,
    M6.Transfer.actualTraceStorage, M6.Transfer.traceStorageModel,
    M6.Transfer.queryCoefficientBits, hlen]
  repeat first
    | exact le_rfl
    | exact hRS
    | exact hp
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | apply max_le_max
