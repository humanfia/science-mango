import FrozenTarget_568f32e14c6a819e
theorem M6.RecipeIsometries.exchange_laws : QuantumHarnessFrozenTarget := by
  intro N inst a b h z
  constructor
  · rfl
  · unfold M6.Physical.syndrome M6.RecipeIsometries.exchange
    funext i
    exact add_comm _ _
