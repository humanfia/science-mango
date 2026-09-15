import FrozenTarget_1b46079420b72e1e
theorem M6.RecipeIsometries.multiplied_syndrome : QuantumHarnessFrozenTarget := by
  intro N _ u a b z
  unfold M6.Physical.syndrome M6.RecipeIsometries.multiplyWord
  dsimp only
  rw [M6.RecipeIsometries.conv_multiply, M6.RecipeIsometries.conv_multiply]
  rfl
