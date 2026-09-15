import FrozenTarget_0a3e627a98eef971
theorem M6.RecipeIsometries.translated_boundary : QuantumHarnessFrozenTarget := by
  intro N inst r s a b h
  have ha := M6.RecipeIsometries.conv_shift N r 0 a h
  have hb := M6.RecipeIsometries.conv_shift N s 0 b h
  simp only [(M6.RecipeIsometries.shift_laws N 0 h).1, add_zero] at ha hb
  simp only [M6.Physical.boundary, M6.RecipeIsometries.translateWord, ha, hb]
