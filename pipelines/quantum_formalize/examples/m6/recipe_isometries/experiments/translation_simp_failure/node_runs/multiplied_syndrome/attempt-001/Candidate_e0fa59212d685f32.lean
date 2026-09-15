import FrozenTarget_e0fa59212d685f32
theorem M6.RecipeIsometries.multiplied_syndrome : QuantumHarnessFrozenTarget := by
  intro N _ u a b z
   dsimp only [M6.Physical.syndrome, M6.RecipeIsometries.multiplyWord]
   rw [M6.RecipeIsometries.conv_multiply, M6.RecipeIsometries.conv_multiply] <;> rfl
