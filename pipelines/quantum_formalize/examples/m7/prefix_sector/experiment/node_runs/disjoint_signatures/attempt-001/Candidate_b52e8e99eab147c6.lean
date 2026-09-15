import FrozenTarget_b52e8e99eab147c6
theorem M7.PrefixSector.disjoint_signatures : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N w F G A B WA WB hFG
    apply Finset.disjoint_left.mpr
    intro p hpF hpG
    simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hpF hpG
    aesop
