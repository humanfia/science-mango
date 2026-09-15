import FrozenTarget_343c3025a315b75a
theorem M7.CyclicSubstitution.hom_polynomial : QuantumHarnessFrozenTarget := by
  intro N inst u h p
  simpa [M7.CyclicSubstitution.hom, M6.Cyclic.image] using
    (AdjoinRoot.lift_mk (AdjoinRoot.of (M6.Cyclic.modulus N))
      (M7.CyclicSubstitution.point u) h p)
