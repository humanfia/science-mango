import FrozenTarget_a7a6a73d0b40edef
theorem M6.RecipeIsometries.multiplied_syndrome : QuantumHarnessFrozenTarget := by
  intros
  simp only [M6.Physical.syndrome, M6.RecipeIsometries.multiplyWord,
    Prod.fst, Prod.snd, M6.RecipeIsometries.conv_multiply] <;> rfl
