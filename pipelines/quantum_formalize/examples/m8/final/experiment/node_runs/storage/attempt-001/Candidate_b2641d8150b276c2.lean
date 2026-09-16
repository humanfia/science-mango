import FrozenTarget_b2641d8150b276c2
theorem M8.Final.storage : QuantumHarnessFrozenTarget := by
  change M8.Final.Storage
  unfold M8.Final.Storage
  exact ⟨M8.SequentialStore.allocation_access, M8.SequentialStore.store_space⟩
