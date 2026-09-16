import FrozenTarget_dc3a5a65d264b39d
theorem M8.CoverageFoundation.consecutive_full : QuantumHarnessFrozenTarget := by
  intro N inst A a ha ha1
  change AddSubgroup.closure (M7.Connectivity.differences A) = ⊤
  apply (M7.Connectivity.one_mem_top N _).mp
  apply AddSubgroup.subset_closure
  unfold M7.Connectivity.differences
  refine ⟨a + 1, ha1, a, ha, ?_⟩
  simp [add_comm]
