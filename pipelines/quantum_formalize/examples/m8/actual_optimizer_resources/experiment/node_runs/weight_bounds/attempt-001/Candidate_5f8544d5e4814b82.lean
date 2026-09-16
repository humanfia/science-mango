import FrozenTarget_5f8544d5e4814b82
theorem M8.OptimizerResources.weight_bounds : QuantumHarnessFrozenTarget := by
  intro N inst a b pins character i m t
  cases character with
  | false =>
      simp only [M8.OptimizerResources.weight, Bool.false_eq_true, if_false,
        M6.ActualTransfer.boundaryWeight]
      apply M6.Transfer.boundary_edge_bounds
  | true =>
      simp only [M8.OptimizerResources.weight, if_true,
        M6.ActualTransfer.characterWeight]
      apply M6.Transfer.character_edge_bounds
