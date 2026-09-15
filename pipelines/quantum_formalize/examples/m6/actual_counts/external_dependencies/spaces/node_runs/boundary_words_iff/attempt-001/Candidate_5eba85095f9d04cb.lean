import FrozenTarget_5eba85095f9d04cb
theorem M6.Spaces.boundary_words_iff : QuantumHarnessFrozenTarget := by
  intro N inst a b v
  classical
  simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords, M6.Spaces.B,
    LinearMap.mem_range, M6.Spaces.boundary_eval]
