import FrozenTarget_dbd1d8f71037c8a6
theorem M6.FixedSpan.recipe_degree : QuantumHarnessFrozenTarget := by
  change M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
  unfold M6.FixedSpan.recipe
  constructor
  · monicity
  · compute_degree
