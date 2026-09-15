import FrozenTarget_890e72df09ec5a93
theorem M6.Spaces.cycle_words_iff : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  rw [M6.Flatten.cycle_orthogonal]
  simp only [M6.Spaces.cycleWords, M6.Character.dualWords,
    Finset.mem_filter, Finset.mem_univ, true_and,
    M6.Character.Orthogonal, M6.Spaces.D, LinearMap.mem_range]
  constructor
  · intro hv h
    exact hv _ ⟨h, rfl⟩
  · rintro hv q ⟨h, rfl⟩
    exact hv h
