import FrozenTarget_671d88dd2af075c6
theorem M8.Solver.optimizer_present : QuantumHarnessFrozenTarget := by
  intro N inst c w hw hvalid hsignature choice hdiscover hnone
  have hanchored : M8.PhysicalBridge.Anchored (M7.Action.act (M8.Discovery.action choice) c) :=
    M8.Discovery.anchored N c choice hdiscover
  exact hsignature ((M8.PhysicalBridge.noLogical N c (M8.Discovery.action choice) w hvalid hanchored).mp hnone)
