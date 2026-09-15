import FrozenTarget_1c6973d908d9d6b4
theorem M6.RecipeIsometries.exchange_laws : QuantumHarnessFrozenTarget := by
  intro N inst a b h z
  constructor
  · rfl
  · unfold M6.Physical.syndrome M6.RecipeIsometries.exchange
    funext i
    exact add_comm _ _
