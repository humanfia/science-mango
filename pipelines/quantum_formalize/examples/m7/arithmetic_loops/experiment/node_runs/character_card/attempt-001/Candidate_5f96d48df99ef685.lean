import FrozenTarget_5f96d48df99ef685
theorem M7.ArithmeticLoops.character_card : QuantumHarnessFrozenTarget := by
  change ∀ D : ℕ, Fintype.card (Fin D → ZMod 2) = 2 ^ D
  intro D
  simp [Fintype.card_fun, ZMod.card]
