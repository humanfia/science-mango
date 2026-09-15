import FrozenTarget_ad5071985ec6f87c
theorem M7.PrefixOrbit.residual_card : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hE hbase bases hbases hnorm
  rw [M7.PrefixOrbit.residual_eq N w E A B WA WB hE hbase bases hbases]
  exact M7.OrbitResidual.subtraction_card N
    (M7.ResiduePrefix.completed N w E A B WA WB) bases
    (M7.CanonicalClasses.normalized_separated N bases hnorm)
