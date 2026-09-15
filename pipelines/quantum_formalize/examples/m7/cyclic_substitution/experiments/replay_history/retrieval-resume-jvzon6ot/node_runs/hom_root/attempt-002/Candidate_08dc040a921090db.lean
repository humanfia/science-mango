import FrozenTarget_08dc040a921090db
theorem M7.CyclicSubstitution.hom_root : QuantumHarnessFrozenTarget := by
  intro N inst u h
  unfold M7.CyclicSubstitution.hom M7.CyclicSubstitution.rho
  exact AdjoinRoot.lift_root h
