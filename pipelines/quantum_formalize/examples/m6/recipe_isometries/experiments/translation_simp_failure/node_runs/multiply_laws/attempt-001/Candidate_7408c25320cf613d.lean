import FrozenTarget_7408c25320cf613d
theorem M6.RecipeIsometries.multiply_laws : QuantumHarnessFrozenTarget := by
  intro N inst u a
  have hinv : M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a := by
    funext i
    simp [M6.RecipeIsometries.multiply, ← mul_assoc]
  refine ⟨?_, hinv, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.multiply]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) := hinv.symm
        _ = M6.RecipeIsometries.multiply N (u⁻¹) 0 := congrArg (M6.RecipeIsometries.multiply N (u⁻¹)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl
