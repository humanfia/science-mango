import FrozenTarget_b8a8e4702bd1ab53
theorem M7.RecipeSignature.source_orbit_quotient : QuantumHarnessFrozenTarget := by
  intro N inst c E L R
  have h := M7.ActualFactorized.exact_orbit_quotient N c
    (M7.RecipeSignature.region E) L R
    (M7.RecipeSignature.translation_invariant N E)
  simpa only [M7.RecipeSignature.sourceCount,
    M7.RecipeSignature.sourceNumerator, M7.RecipeSignature.region,
    M7.RecipeSignature.outer_source_signature] using h
