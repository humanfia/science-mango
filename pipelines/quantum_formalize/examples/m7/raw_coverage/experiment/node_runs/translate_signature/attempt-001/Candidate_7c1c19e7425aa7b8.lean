import FrozenTarget_7c1c19e7425aa7b8
theorem M7.RawCoverage.translate_signature : QuantumHarnessFrozenTarget := by
  intro N inst c s t
  exact (M7.RecipeSignature.translation_invariant N (fun F => F = M7.RecipeSignature.signature c) _ _ _).mpr rfl
