import FrozenTarget_93d6a88515562725
theorem M6.FixedSpan.nontrivial_family : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro k
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    have hg : ({0, 1, 2} : Finset ℕ).gcd id = 1 := by decide
    rw [hg]
    simp
  · rw [M6.FixedSpan.recipe_signature (3 * (k + 1)) ⟨k + 1, rfl⟩]
    exact M6.FixedSpan.recipe_degree.2
