import FrozenTarget_22ed598cf3e15fb5
theorem M6.FixedSpan.nontrivial_family : QuantumHarnessFrozenTarget := by
  change ∀ k : ℕ, let N := 3 * (k + 1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2
  intro k
   dsimp only
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · norm_num [M6.FixedSpan.recipe_support]
  · simp [M6.FixedSpan.recipe_support]
  · simp [M6.FixedSpan.recipe_support, Finset.gcd_insert, Finset.gcd_singleton]
  · rw [M6.FixedSpan.recipe_signature (3 * (k + 1)) ⟨k + 1, rfl⟩]
    exact M6.FixedSpan.recipe_degree.2
