import FrozenTarget_e2d41426d7d27471
theorem M8.OptimizerResources.indexed_guarantee : QuantumHarnessFrozenTarget := by
  intro N inst a b pins character hspan
  have hlt : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt hspan ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  cases character with
  | false =>
      simpa [M8.OptimizerResources.weight] using
        (M6.ActualTransfer.boundary_indexed_resources N a b pins hlt)
  | true =>
      simpa [M8.OptimizerResources.weight] using
        (M6.ActualTransfer.character_indexed_resources N a b pins hlt)
