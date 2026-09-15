import FrozenTarget_9d0b71ac2f681cc4
theorem M7.ClosedSolve.closed_pointwise : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N w inst c hA hB h0A h0B hc
  have hadm := M7.Connectivity.connected_admissible N w c hA hB h0A h0B hc
  exact M6.Final.original_m6.1 N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) hadm
