import FrozenTarget_c9fe3c20dc56dd00
theorem M7.PrefixSector.overfull_zero : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N w E A B WA WB h
    rcases h with hA | hB
    · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC,
        hA, Nat.not_le_of_lt hA]
    · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC,
        hB, Nat.not_le_of_lt hB]
