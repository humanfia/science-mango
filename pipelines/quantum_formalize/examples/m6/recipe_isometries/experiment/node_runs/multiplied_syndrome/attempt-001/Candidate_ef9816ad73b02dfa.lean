import FrozenTarget_ef9816ad73b02dfa
theorem M6.RecipeIsometries.multiplied_syndrome : QuantumHarnessFrozenTarget := by
  intro N _ u a b z
  unfold M6.Physical.syndrome M6.RecipeIsometries.multiplyWord
  dsimp only
  rw [M6.RecipeIsometries.conv_multiply, M6.RecipeIsometries.conv_multiply]
  rfl
