import FrozenTarget_0644a2a93e88c2ef
theorem M7.QuotientAuto.substitution_comp : QuantumHarnessFrozenTarget := by
  intro N inst u v
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp only [RingHom.comp_apply, M7.QuotientAuto.substitution_scalars]
  · change M7.QuotientAuto.substitution v (M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N)) = M7.QuotientAuto.substitution (v * u) (M7.CyclicSubstitution.rho N)
    rw [M7.QuotientAuto.substitution_root, M7.QuotientAuto.substitution_root]
    change M7.QuotientAuto.substitution v (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) = M7.CyclicSubstitution.point (v * u)
    rw [map_pow, M7.QuotientAuto.substitution_root]
    simpa only [mul_comm] using M7.CyclicSubstitution.point_mul N v u
