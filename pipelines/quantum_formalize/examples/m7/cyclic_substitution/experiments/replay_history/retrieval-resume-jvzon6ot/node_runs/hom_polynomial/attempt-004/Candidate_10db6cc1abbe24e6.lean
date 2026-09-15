import FrozenTarget_10db6cc1abbe24e6
theorem M7.CyclicSubstitution.hom_polynomial : QuantumHarnessFrozenTarget := by
  intro N inst u h p
  change AdjoinRoot.lift (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.point u) h (AdjoinRoot.mk (M6.Cyclic.modulus N) p) = _
  exact AdjoinRoot.lift_mk _ _ _ _
