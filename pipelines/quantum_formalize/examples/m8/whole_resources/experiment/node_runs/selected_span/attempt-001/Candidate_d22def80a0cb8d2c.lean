import FrozenTarget_d22def80a0cb8d2c
theorem M8.WholeResources.selected_span : QuantumHarnessFrozenTarget := by
  intro N inst c w hw hc choice hchoice
  have hv : M8.PhysicalBridge.Valid w (M8.Discovery.transformed c choice) := by
    unfold M8.Discovery.transformed
    unfold M8.PhysicalBridge.Valid at *
    aesop (add safe apply [M7.Action.support_cards, M7.Connectivity.connected_action]) (add simp [M7.Action.support_cards, M7.Connectivity.connected_action])
  exact (M8.Solver.literal_span_le N (M8.Discovery.transformed c choice) w hw hv).trans
    (M8.Discovery.cutoff N c choice hchoice)
