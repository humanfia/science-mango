import FrozenTarget_76901bf71c3cd9f7
theorem M5.PhysicalRecovery.actual_split : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length < M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PhysicalRecovery.oracle N w F (p ++ [false]) + M5.PhysicalRecovery.oracle N w F (p ++ [true])
  intro N w F hN hw hF hFN p hp
  have hchild (b : Bool) : (p ++ [b]).length ≤ M5.PhysicalRecovery.decisionCount N := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN p (Nat.le_of_lt hp),
    M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN (p ++ [false]) (hchild false),
    M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN (p ++ [true]) (hchild true)]
  simpa [Fintype.sum_bool, add_comm] using
    (M5.PrefixPartition.count_partition Bool (M5.PhysicalRecovery.validWords N w F)
      (M5.PhysicalRecovery.decisionCount N) p
      (fun q hq => M5.PhysicalRecovery.valid_words_length N w F q hq) hp)
