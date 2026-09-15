import FrozenTarget_be4769ee61433a13
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  intro N inst
  have h := Fintype.card_congr (show M7.Action.Record N ≃ _ from
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; rcases p with ⟨u, e, s, t⟩; rfl })
  constructor
  · rw [h]
    simp [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient,
      pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · simp [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient,
      pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
