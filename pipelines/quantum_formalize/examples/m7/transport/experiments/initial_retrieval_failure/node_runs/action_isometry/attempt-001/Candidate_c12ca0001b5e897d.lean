import FrozenTarget_c12ca0001b5e897d
theorem M7.Transport.action_isometry : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  rcases g with ⟨u, s, t, e⟩
  cases e <;>
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX,
      M7.Action.act, Bool.false_eq_true, ↓reduceIte, Prod.fst, Prod.snd,
      M7.Transport.affine_indicator] <;>
    grind [M6.RecipeIsometries.translation_isometry,
      M6.RecipeIsometries.multiplier_isometry,
      M6.RecipeIsometries.exchange_isometry, Function.Bijective.comp]
