import FrozenTarget_c3e6847acf0ba58b
theorem M7.Transport.action_isometry : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  rcases g with ⟨u, e, s, t⟩
  have htB := fun a b s t v => (M6.RecipeIsometries.translation_isometry N a b s t).2 v |>.1
  have htC := fun a b s t v => (M6.RecipeIsometries.translation_isometry N a b s t).2 v |>.2.1
  have htW := fun a b s t v => (M6.RecipeIsometries.translation_isometry N a b s t).2 v |>.2.2
  have hmB := fun a b u v => (M6.RecipeIsometries.multiplier_isometry N a b u).2 v |>.1
  have hmC := fun a b u v => (M6.RecipeIsometries.multiplier_isometry N a b u).2 v |>.2.1
  have hmW := fun a b u v => (M6.RecipeIsometries.multiplier_isometry N a b u).2 v |>.2.2
  have heB := fun a b v => (M6.RecipeIsometries.exchange_isometry N a b).2 v |>.1
  have heC := fun a b v => (M6.RecipeIsometries.exchange_isometry N a b).2 v |>.2.1
  have heW := fun a b v => (M6.RecipeIsometries.exchange_isometry N a b).2 v |>.2.2
  cases e <;>
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX,
      M7.Action.act, Bool.false_eq_true, ↓reduceIte,
      M7.Transport.affine_indicator, htB, htC, hmB, hmC, heB, heC]
  all_goals
    constructor
    · repeat first
        | exact (M6.RecipeIsometries.translation_isometry N 0 0 _ _).1
        | exact (M6.RecipeIsometries.multiplier_isometry N 0 0 _).1
        | exact (M6.RecipeIsometries.exchange_isometry N 0 0).1
        | apply Function.Bijective.comp
    · intro v
      simp only [htB, htC, hmB, hmC, heB, heC, htW, hmW, heW, and_self]
