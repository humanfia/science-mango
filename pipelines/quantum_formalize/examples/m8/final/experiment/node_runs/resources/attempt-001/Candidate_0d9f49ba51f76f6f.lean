import FrozenTarget_0d9f49ba51f76f6f
theorem M8.Final.resources : QuantumHarnessFrozenTarget := by
  change M8.Final.Resources
  unfold M8.Final.Resources
  exact ⟨M8.SequentialResources.actual_prefix_charge, M8.SequentialResources.sequential_bound⟩
