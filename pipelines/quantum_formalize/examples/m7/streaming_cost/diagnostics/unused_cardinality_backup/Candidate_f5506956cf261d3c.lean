import FrozenTarget_f5506956cf261d3c
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  intro N inst
  classical
  let e : M7.Action.Record N ≃ (ZMod N)ˣ × Bool × ZMod N × ZMod N :=
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; rcases p with ⟨u, b, s, t⟩; rfl }
  constructor
  · rw [Fintype.card_congr e]
    simp [M7.StreamingCost.recordCount, Fintype.card_prod, ZMod.card, pow_two]
    <;> ring
  · simp [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient]
