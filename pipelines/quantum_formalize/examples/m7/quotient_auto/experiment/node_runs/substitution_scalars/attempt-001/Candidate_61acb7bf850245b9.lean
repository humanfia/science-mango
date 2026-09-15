import FrozenTarget_61acb7bf850245b9
theorem M7.QuotientAuto.substitution_scalars : QuantumHarnessFrozenTarget := by
  intro N inst u r
  unfold M7.QuotientAuto.substitution M7.CyclicSubstitution.hom
  exact AdjoinRoot.lift_of (M7.CyclicSubstitution.point_root N u)
