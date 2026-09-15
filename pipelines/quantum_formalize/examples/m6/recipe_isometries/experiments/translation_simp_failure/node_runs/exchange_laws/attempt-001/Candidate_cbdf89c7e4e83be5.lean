import FrozenTarget_cbdf89c7e4e83be5
theorem M6.RecipeIsometries.exchange_laws : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h z
  constructor
  · rfl
  · simp [M6.Physical.syndrome, M6.RecipeIsometries.exchange, add_comm]
