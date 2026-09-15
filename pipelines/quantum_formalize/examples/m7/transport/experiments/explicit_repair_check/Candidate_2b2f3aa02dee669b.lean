import FrozenTarget_2b2f3aa02dee669b
theorem M7.Transport.action_isometry : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  rcases g with ⟨u, e, s, t⟩
  cases e
  · have hm := M6.RecipeIsometries.multiplier_isometry N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2) u
    have ht := M6.RecipeIsometries.translation_isometry N
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.1))
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.2)) s t
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX, M7.Action.act,
      Bool.false_eq_true, Bool.true_eq_false, reduceIte, M7.Transport.affine_indicator]
    refine ⟨ht.1.comp hm.1, ?_⟩
    intro v
    have htV := ht.2 (M6.RecipeIsometries.multiplier N u v)
    have hmV := hm.2 v
    exact ⟨htV.1.trans hmV.1, htV.2.1.trans hmV.2.1, htV.2.2.trans hmV.2.2⟩
  · have hm := M6.RecipeIsometries.multiplier_isometry N (M7.Supports.indicator c.2) (M7.Supports.indicator c.1) u
    have ht := M6.RecipeIsometries.translation_isometry N
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.2))
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.1)) s t
    have he := M6.RecipeIsometries.exchange_isometry N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX, M7.Action.act,
      Bool.false_eq_true, Bool.true_eq_false, reduceIte, M7.Transport.affine_indicator]
    refine ⟨ht.1.comp (hm.1.comp he.1), ?_⟩
    intro v
    have htV := ht.2 (M6.RecipeIsometries.multiplier N u (M6.RecipeIsometries.blockExchange N v))
    have hmV := hm.2 (M6.RecipeIsometries.blockExchange N v)
    have heV := he.2 v
    exact ⟨htV.1.trans (hmV.1.trans heV.1), htV.2.1.trans (hmV.2.1.trans heV.2.1), htV.2.2.trans (hmV.2.2.trans heV.2.2)⟩
