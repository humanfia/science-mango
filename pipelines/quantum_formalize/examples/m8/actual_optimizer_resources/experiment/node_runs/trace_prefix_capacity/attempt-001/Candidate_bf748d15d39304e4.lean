import FrozenTarget_bf748d15d39304e4
theorem M8.OptimizerResources.trace_prefix_capacity : QuantumHarnessFrozenTarget := by
  intro N inst a b pins character hcut k d
  have h := M6.Transfer.actual_trace_intermediates
    (M6.ActualTransfer.span a b) N
    (M8.OptimizerResources.weight N a b pins character) k d
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).1)
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).2)
  exact ⟨h, lt_of_le_of_lt h (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hcut)⟩
