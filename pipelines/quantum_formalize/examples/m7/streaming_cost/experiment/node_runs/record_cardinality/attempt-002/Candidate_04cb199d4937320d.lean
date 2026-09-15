import FrozenTarget_04cb199d4937320d
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.StreamingCost.recordCount N = Fintype.card (M7.Action.Record N) ∧ M7.StreamingCost.recordCount N = 2 * Nat.totient N * N^2
  intro N inst
  classical
  have h := Fintype.card_congr (show M7.Action.Record N ≃ ((ZMod N)ˣ × Bool × ZMod N × ZMod N) from
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by rintro ⟨u, e, s, t⟩; rfl })
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card, ZMod.card_units_eq_totient] at h
  constructor
  · rw [h]
    simp only [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient]
    ring
  · simp only [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient]
    ring
