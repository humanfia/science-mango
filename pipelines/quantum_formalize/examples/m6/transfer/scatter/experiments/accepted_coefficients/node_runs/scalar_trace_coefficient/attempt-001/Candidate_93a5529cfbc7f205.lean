import FrozenTarget_93a5529cfbc7f205
theorem M6.Transfer.scalar_trace_coefficient : QuantumHarnessFrozenTarget := by
  classical
  intro R N W d hW
  unfold M6.Transfer.scalarTraceCoefficient M6.Transfer.arrayTrace
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro start hstart
  rw [M6.Transfer.scalar_layers_exact R N W start N hW]
  rfl
