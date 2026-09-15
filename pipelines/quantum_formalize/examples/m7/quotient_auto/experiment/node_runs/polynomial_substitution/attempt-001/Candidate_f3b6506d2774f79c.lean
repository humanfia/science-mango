import FrozenTarget_f3b6506d2774f79c
theorem M7.QuotientAuto.polynomial_substitution : QuantumHarnessFrozenTarget := by
  intro N inst u p
  unfold M7.QuotientAuto.substitution
  rw [M7.CyclicSubstitution.hom_polynomial]
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (p.comp (Polynomial.X ^ (u : ZMod N).val)) = _
  rw [← AdjoinRoot.eval₂_root]
  simp only [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    M7.CyclicSubstitution.point, M7.CyclicSubstitution.rho]
