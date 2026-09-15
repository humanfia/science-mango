import FrozenTarget_952bb9b8a2ba682a
theorem M6.Spaces.logical_words_iff : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  simp only [M6.Spaces.logicalWords, Finset.mem_sdiff,
    M6.Spaces.cycle_words_iff, M6.Spaces.boundary_words_iff]
