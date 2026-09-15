import FrozenTarget_d9296df633da79df
theorem M6.Final.counting_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b
  intro N inst a b h
  unfold M6.Final.Admissible at h
  unfold M6.Final.CountingCorrect
  simp only [M6.Final.LX, M6.Final.BX, M6.Final.CX]
  repeat' constructor
  all_goals intros
  all_goals exact?
