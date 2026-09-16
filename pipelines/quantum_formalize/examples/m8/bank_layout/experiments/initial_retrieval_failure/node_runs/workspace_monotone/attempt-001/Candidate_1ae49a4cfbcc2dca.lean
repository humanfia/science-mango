import FrozenTarget_1ae49a4cfbcc2dca
theorem M8.BankLayout.workspace_monotone : QuantumHarnessFrozenTarget := by
  change ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots
  intro R S N slots hRS
  have hpow : (2 : ℕ)^R ≤ 2^S := pow_le_pow_right₀ (by decide) hRS
  unfold M6.Transfer.solveStorage M6.Transfer.pairedQueryStorage M6.Transfer.actualTraceStorage M6.Transfer.traceStorageModel
  simp only [M6.Transfer.scatterEventList, Finset.length_toList, Finset.card_univ,
    M6.Transfer.ScatterEvent, Fintype.card_prod, M6.Transfer.state_count,
    M6.Transfer.Bit, ZMod.card, Fintype.card_fin]
  repeat first
    | exact le_rfl
    | exact hRS
    | exact hpow
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | apply max_le_max
