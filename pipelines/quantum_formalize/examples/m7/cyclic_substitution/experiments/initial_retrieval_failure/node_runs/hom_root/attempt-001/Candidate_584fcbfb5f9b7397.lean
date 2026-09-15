import FrozenTarget_584fcbfb5f9b7397
theorem M7.CyclicSubstitution.hom_root : QuantumHarnessFrozenTarget := by
  intro N inst u h
  simpa only [M7.CyclicSubstitution.hom, M7.CyclicSubstitution.rho] using
    (AdjoinRoot.lift_root (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.point u) h)
