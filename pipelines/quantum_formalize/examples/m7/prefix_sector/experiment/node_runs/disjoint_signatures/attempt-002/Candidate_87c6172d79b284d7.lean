import FrozenTarget_87c6172d79b284d7
theorem M7.PrefixSector.disjoint_signatures : QuantumHarnessFrozenTarget := by
  classical
  intro N w F G A B WA WB hFG
  apply Finset.disjoint_left.mpr
  intro p hpF hpG
  simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hpF hpG
  aesop
