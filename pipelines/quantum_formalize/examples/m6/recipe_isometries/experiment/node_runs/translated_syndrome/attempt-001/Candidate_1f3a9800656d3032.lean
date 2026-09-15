import FrozenTarget_1f3a9800656d3032
theorem M6.RecipeIsometries.translated_syndrome : QuantumHarnessFrozenTarget := by
  intro N inst r s a b z
  change M6.Physical.conv N (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.shift N r z.1) + M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s z.2) = M6.RecipeIsometries.shift N (r + s) (M6.Physical.conv N b z.1 + M6.Physical.conv N a z.2)
  rw [M6.RecipeIsometries.conv_shift, M6.RecipeIsometries.conv_shift, add_comm s r]
  rfl
