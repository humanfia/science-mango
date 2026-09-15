import FrozenTarget_288f3b67247725f5
theorem M7.CyclicSubstitution.hom_polynomial : QuantumHarnessFrozenTarget := by
  by
    intro N inst u h p
    change AdjoinRoot.lift (AdjoinRoot.of (M6.Cyclic.modulus N))
      (M7.CyclicSubstitution.point u) h
      (AdjoinRoot.mk (M6.Cyclic.modulus N) p) = _
    exact AdjoinRoot.lift_mk h p
