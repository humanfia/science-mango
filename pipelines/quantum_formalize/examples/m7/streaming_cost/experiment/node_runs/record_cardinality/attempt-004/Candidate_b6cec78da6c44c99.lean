import FrozenTarget_b6cec78da6c44c99
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.StreamingCost.recordCount N = Fintype.card (M7.Action.Record N) ∧ M7.StreamingCost.recordCount N = 2 * Nat.totient N * N^2
  intro N _
  constructor <;> simp [M7.StreamingCost.recordCount, M7.Action.record_card, ZMod.card_units_eq_totient, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
