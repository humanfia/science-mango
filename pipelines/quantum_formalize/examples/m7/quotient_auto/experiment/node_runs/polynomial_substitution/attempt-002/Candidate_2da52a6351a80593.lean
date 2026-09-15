import FrozenTarget_2da52a6351a80593
theorem M7.QuotientAuto.polynomial_substitution : QuantumHarnessFrozenTarget := by
  intro N inst u p
  unfold M7.QuotientAuto.substitution
  rw [M7.CyclicSubstitution.hom_polynomial]
  unfold M6.Cyclic.image
  rw [← AdjoinRoot.aeval_eq]
  simp only [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq,
    Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rfl
