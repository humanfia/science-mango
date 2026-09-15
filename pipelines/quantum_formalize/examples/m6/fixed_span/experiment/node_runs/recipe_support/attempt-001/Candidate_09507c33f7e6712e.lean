import FrozenTarget_09507c33f7e6712e
theorem M6.FixedSpan.recipe_support : QuantumHarnessFrozenTarget := by
  classical
  change M6.FixedSpan.recipe.support = {0, 1, 2}
  ext n
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;>
    simp_all [M6.FixedSpan.recipe, Polynomial.mem_support_iff,
      Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow, eq_comm]
