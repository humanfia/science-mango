import FrozenTarget_71ef2415b2eb5133
theorem M7.PrefixSector.completion_membership : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB x
  simp only [M7.PrefixSector.completions, Finset.mem_biUnion]
