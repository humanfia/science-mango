import FrozenTarget_f01ca8f2fe3ea9a6
theorem M5.PhysicalRecovery.actual_terminal : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length = M5.PhysicalRecovery.decisionCount N → 0 < M5.PhysicalRecovery.oracle N w F p → M5.PhysicalRecovery.wordValid N w F p
  intro N w F hN hw hF hFN p hp hpos
  rw [M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN p hp.le] at hpos
  rw [M5.PrefixPartition.count_terminal Bool (M5.PhysicalRecovery.validWords N w F)
    (M5.PhysicalRecovery.decisionCount N) p
    (fun q hq => M5.PhysicalRecovery.valid_words_length N w F q hq) hp] at hpos
  by_cases hm : p ∈ M5.PhysicalRecovery.validWords N w F
  · exact (Finset.mem_filter.mp hm).2
  · simp [hm] at hpos
