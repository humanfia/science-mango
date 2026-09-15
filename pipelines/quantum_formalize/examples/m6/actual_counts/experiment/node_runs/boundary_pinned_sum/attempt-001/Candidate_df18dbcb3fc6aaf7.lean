import FrozenTarget_df18dbcb3fc6aaf7
theorem M6.ActualCounts.boundary_pinned_sum : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b ha hb P
  simpa [M6.ActualCounts.boundaryInputSum, M6.Character.pinnedMonomial,
    M6.Pinned.enumerator, Finset.sum_filter, M6.Spaces.boundary_eval] using
    (M6.ActualCounts.boundary_weighted_sum N a b ha hb
      (M6.Character.pinnedMonomial P))
