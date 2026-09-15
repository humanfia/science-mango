import FrozenTarget_113a0d06f9ac0aca
theorem M6.RecipeIsometries.translated_syndrome : QuantumHarnessFrozenTarget := by
  intro N inst r s a b z
  simp only [M6.Physical.syndrome, M6.RecipeIsometries.translateWord,
    Prod.fst, Prod.snd, M6.RecipeIsometries.conv_shift, add_comm s r] <;> rfl
