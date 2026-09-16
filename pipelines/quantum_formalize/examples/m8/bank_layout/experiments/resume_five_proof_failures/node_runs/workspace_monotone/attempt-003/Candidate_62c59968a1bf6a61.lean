import FrozenTarget_62c59968a1bf6a61
theorem M8.BankLayout.workspace_monotone : QuantumHarnessFrozenTarget := by
  change ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots
  intro R S N slots hRS
  have hp : 2 ^ R ≤ (2 : ℕ) ^ S := pow_le_pow_right₀ (by decide) hRS
  unfold M6.Transfer.solveStorage M6.Transfer.pairedQueryStorage M6.Transfer.actualTraceStorage M6.Transfer.traceStorageModel
  simp [M6.Transfer.scatterEventList, M6.Transfer.ScatterEvent, M6.Transfer.state_count, M6.Transfer.Bit]
  repeat' first
    | exact le_rfl
    | exact hRS
    | exact hp
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | apply Nat.pow_le_pow_left
    | omega
