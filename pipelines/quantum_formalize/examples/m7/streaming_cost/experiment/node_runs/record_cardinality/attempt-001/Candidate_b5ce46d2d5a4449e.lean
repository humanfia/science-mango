import FrozenTarget_b5ce46d2d5a4449e
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.StreamingCost.recordCount N = Fintype.card (M7.Action.Record N) ∧ M7.StreamingCost.recordCount N = 2 * Nat.totient N * N^2
  intro N inst
  constructor <;> simp only [M7.StreamingCost.recordCount, M7.Action.record_card, ZMod.card_units_eq_totient] <;> ring
