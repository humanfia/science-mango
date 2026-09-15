import FrozenTarget_7a4e6da0fbe3863d
theorem M7.PrefixSector.overfull_zero : QuantumHarnessFrozenTarget := by
  intro N w E A B WA WB h
  classical
  change M7.PrefixSector.count N w E A B WA WB = 0
  rcases h with hA | hB
  · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC, hA, Nat.not_le_of_lt hA]
  · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC, hB, Nat.not_le_of_lt hB]
