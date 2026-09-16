import FrozenTarget_42abd6aeb88344d7
theorem M8.MixedNonproduct.word_action : QuantumHarnessFrozenTarget := by
  classical
  intro N inst g c
  have h := M7.Transport.action_isometry (N := N) (g := g) (c := c)
  simp_all [M8.MixedNonproduct.wordAction, M8.MixedNonproduct.Cycles,
    M7.Transport.Xmap, M6.RecipeIsometries.lift,
    M6.Spaces.cycle_words_iff]
  <;> aesop
