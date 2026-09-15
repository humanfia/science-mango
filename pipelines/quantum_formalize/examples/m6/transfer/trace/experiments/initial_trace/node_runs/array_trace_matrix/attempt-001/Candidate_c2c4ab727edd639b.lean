import FrozenTarget_c2c4ab727edd639b
theorem M6.Transfer.array_trace_matrix : QuantumHarnessFrozenTarget := by
  classical
  intro R K inst W N
  change (∑ start : M6.Transfer.Memory R, M6.Transfer.layers W start N start) =
    ∑ start : M6.Transfer.Memory R, M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N start start
  apply Finset.sum_congr rfl
  intro start hstart
  exact M6.Transfer.layers_matrix R K W start start N
