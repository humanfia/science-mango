import FrozenTarget_b739e14a666fa388
theorem M6.Spaces.input_card : QuantumHarnessFrozenTarget := by
  intro N inst
  change Nat.card (ZMod N → ZMod 2) = 2 ^ N
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
