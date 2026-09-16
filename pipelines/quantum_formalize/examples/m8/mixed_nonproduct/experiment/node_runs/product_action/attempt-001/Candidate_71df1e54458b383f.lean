import FrozenTarget_71df1e54458b383f
theorem M8.MixedNonproduct.product_action : QuantumHarnessFrozenTarget := by
    classical
    intro N inst g c
    have forward : ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N),
        M8.MixedNonproduct.Product c → M8.MixedNonproduct.Product (M7.Action.act g c) := by
      intro g c hc
      have hr := (M8.MixedNonproduct.product_rectangular N c).mp hc
      obtain ⟨hb, hw⟩ := M8.MixedNonproduct.word_action N g c
      apply (M8.MixedNonproduct.product_rectangular N (M7.Action.act g c)).mpr
      intro z hz t ht
      obtain ⟨x, rfl⟩ := hb.2 z
      obtain ⟨y, rfl⟩ := hb.2 t
      have hx := (hw x).mp hz
      have hy := (hw y).mp ht
      cases he : g.exchange
      · have hcross : M8.MixedNonproduct.wordAction g (x.1, y.2) =
            ((M8.MixedNonproduct.wordAction g x).1,
             (M8.MixedNonproduct.wordAction g y).2) := by
          simp [M8.MixedNonproduct.wordAction, he,
            M6.RecipeIsometries.translateWord, M6.RecipeIsometries.multiplyWord,
            M6.RecipeIsometries.exchange]
        rw [← hcross]
        exact (hw (x.1, y.2)).mpr (hr x hx y hy)
      · have hcross : M8.MixedNonproduct.wordAction g (y.1, x.2) =
            ((M8.MixedNonproduct.wordAction g x).1,
             (M8.MixedNonproduct.wordAction g y).2) := by
          simp [M8.MixedNonproduct.wordAction, he,
            M6.RecipeIsometries.translateWord, M6.RecipeIsometries.multiplyWord,
            M6.RecipeIsometries.exchange]
        rw [← hcross]
        exact (hw (y.1, x.2)).mpr (hr y hy x hx)
    constructor
    · intro h
      have hi := forward (M7.Action.inverse g) (M7.Action.act g c) h
      rw [M7.Action.act_inverse N g c] at hi
      exact hi
    · exact forward g c
