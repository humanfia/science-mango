import FrozenTarget_c84f2cbe1b69cfb1
theorem M8.OptimizerResources.trace_capacity : QuantumHarnessFrozenTarget := by
  intro N inst a b pins character hcut d
  have hbound : ((M6.Transfer.arrayTrace (M8.OptimizerResources.weight N a b pins character) N).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    apply M6.Transfer.trace_coefficient_bound
    all_goals
      intros
      first
      | exact (M8.OptimizerResources.weight_bounds N a b pins character _ _ _).1
      | exact (M8.OptimizerResources.weight_bounds N a b pins character _ _ _).2
  exact ⟨hbound, lt_of_le_of_lt hbound (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hcut)⟩
