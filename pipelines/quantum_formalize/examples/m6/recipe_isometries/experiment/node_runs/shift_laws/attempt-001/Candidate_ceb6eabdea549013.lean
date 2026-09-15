import FrozenTarget_ceb6eabdea549013
theorem M6.RecipeIsometries.shift_laws : QuantumHarnessFrozenTarget := by
  intro N inst r a
  have hinv (b : M6.RecipeIsometries.Block N) :
      M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r b) = b := by
    funext i
    simp [M6.RecipeIsometries.shift, sub_eq_add_neg, add_assoc]
  refine ⟨?_, hinv a, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.shift]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) := (hinv a).symm
        _ = M6.RecipeIsometries.shift N (-r) 0 := congrArg (M6.RecipeIsometries.shift N (-r)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl
