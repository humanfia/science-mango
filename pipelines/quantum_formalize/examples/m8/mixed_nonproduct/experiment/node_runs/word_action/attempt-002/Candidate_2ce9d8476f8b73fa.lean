import FrozenTarget_2ce9d8476f8b73fa
theorem M8.MixedNonproduct.word_action : QuantumHarnessFrozenTarget := by
  classical
  intro N _ g c
  have hi := M7.Transport.action_isometry N g c
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    first
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_left N)
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_right N)
  have hw : ∀ z : M6.Physical.Word N,
      M6.Flatten.flatten N (M8.MixedNonproduct.wordAction g z) =
        M7.Transport.Xmap g (M6.Flatten.flatten N z) := by
    intro z
    cases he : g.exchange <;>
      simp [M8.MixedNonproduct.wordAction, M7.Transport.Xmap,
        M6.RecipeIsometries.translate, M6.RecipeIsometries.multiplier,
        M6.RecipeIsometries.blockExchange, M6.RecipeIsometries.lift,
        M6.Flatten.flatten_left, M6.Flatten.flatten_right, he]
  constructor
  · have hinj : Function.Injective (M8.MixedNonproduct.wordAction g) := by
      intro x y h
      apply hf
      apply hi.1.1
      rw [← hw x, ← hw y, h]
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  · intro z
    have hc := (hi.2 (M6.Flatten.flatten N z)).2.1
    rw [← hw z] at hc
    simpa [M7.Transport.CX, M8.MixedNonproduct.Cycles,
      M6.Spaces.cycle_words_iff, M6.Flatten.flatten_left,
      M6.Flatten.flatten_right] using hc
