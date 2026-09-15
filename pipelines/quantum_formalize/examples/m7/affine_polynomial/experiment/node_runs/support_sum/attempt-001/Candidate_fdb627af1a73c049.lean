import FrozenTarget_fdb627af1a73c049
theorem M7.AffinePolynomial.support_sum : QuantumHarnessFrozenTarget := by
  intro N inst A
  classical
  simp [M7.AffinePolynomial.image, M7.Supports.polynomial,
    M6.Cyclic.image, M7.CyclicSubstitution.rho, map_sum,
    map_pow, AdjoinRoot.mk_X]
