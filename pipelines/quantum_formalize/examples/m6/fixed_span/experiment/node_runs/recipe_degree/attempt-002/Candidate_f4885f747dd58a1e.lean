import FrozenTarget_f4885f747dd58a1e
theorem M6.FixedSpan.recipe_degree : QuantumHarnessFrozenTarget := by
  change M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
  unfold M6.FixedSpan.recipe
  constructor
  · monicity!
  · compute_degree!
