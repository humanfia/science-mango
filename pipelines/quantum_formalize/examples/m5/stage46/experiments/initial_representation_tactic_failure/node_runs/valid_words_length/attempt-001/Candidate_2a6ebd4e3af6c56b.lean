import FrozenTarget_2a6ebd4e3af6c56b
theorem M5.PhysicalRecovery.valid_words_length : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (q : List Bool), q ∈ M5.PhysicalRecovery.validWords N w F → q.length = M5.PhysicalRecovery.decisionCount N
  intro N w F q h
  classical
  simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter, M5.PhysicalRecovery.wordValid] at h
  tauto
