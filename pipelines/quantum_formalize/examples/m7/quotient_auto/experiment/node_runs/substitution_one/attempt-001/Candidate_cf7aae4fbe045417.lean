import FrozenTarget_cf7aae4fbe045417
theorem M7.QuotientAuto.substitution_one : QuantumHarnessFrozenTarget := by
  intro N inst
  apply AdjoinRoot.ringHom_ext
  · ext r
    exact M7.QuotientAuto.substitution_scalars N (1 : (ZMod N)ˣ) r
  · change M7.QuotientAuto.substitution (1 : (ZMod N)ˣ) (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.rho N
    rw [M7.QuotientAuto.substitution_root, M7.CyclicSubstitution.point_one]
