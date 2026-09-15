import FrozenTarget_83516a44767ecc2e
theorem M7.PrefixOrbit.residual_positive : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hE hbase bases hbases hnorm
  rw [M7.PrefixOrbit.residual_eq N w E A B WA WB hE hbase bases hbases]
  exact M7.OrbitResidual.nonnegative_positive N
    (M7.ResiduePrefix.completed N w E A B WA WB) bases
    (M7.CanonicalClasses.normalized_separated N bases hnorm)
