import FrozenTarget_7ac5d67a222efbc3
theorem M7.PrefixSector.disjoint_sector_sum : QuantumHarnessFrozenTarget := by
  classical
  intro N w E H A B WA WB hEH
  unfold M7.PrefixSector.count
  exact Finset.sum_union hEH
