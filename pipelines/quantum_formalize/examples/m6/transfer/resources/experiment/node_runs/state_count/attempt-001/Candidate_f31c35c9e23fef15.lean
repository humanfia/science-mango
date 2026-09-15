import FrozenTarget_f31c35c9e23fef15
theorem M6.Transfer.state_count : QuantumHarnessFrozenTarget := by
  change ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2 ^ R
  intro R
  simp [M6.Transfer.Memory, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]
