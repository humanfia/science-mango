import FrozenTarget_65156981ae91cd67
theorem M7.PrefixOrbit.residual_eq : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hE hbase bases hbases
  classical
  unfold M7.PrefixOrbit.residual M7.OrbitResidual.subtraction
  rw [M7.ResiduePrefix.count_completed N w E A B WA WB hE hbase]
  simp only [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [M7.PrefixOrbit.source_count N w E A B WA WB hbase c (hbases c hc)]
