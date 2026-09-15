import FrozenTarget_a29a11120b3eb5a6
theorem M7.SignatureIdeal.modulus_zero : QuantumHarnessFrozenTarget := by
  intro N inst
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Cyclic.modulus N) = 0
  exact AdjoinRoot.mk_self
