import FrozenTarget_75afd56f31dc086a
theorem M7.AffinePolynomial.substitution_support_sum : QuantumHarnessFrozenTarget := by
  intro N inst u A
  classical
  rw [M7.AffinePolynomial.support_sum N A]
  simp only [M7.QuotientAuto.substitution, map_sum, map_pow,
    M7.CyclicSubstitution.hom_root]
