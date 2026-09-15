import FrozenTarget_d5ac51184f93394f
theorem M5.PhysicalRecovery.arithmetic_oracle_exact : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p
  intro N w F hN hw hF hFN p hp
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  by_cases hpa : (M5.PhysicalRecovery.selectedA N p).card ≤ w
  · by_cases hpb : (M5.PhysicalRecovery.selectedB N p).card ≤ w
    · have hOK : M5.ConditionalCount.PrefixOK N w
          (M5.PhysicalRecovery.selectedA N p) (M5.PhysicalRecovery.selectedB N p)
          (M5.PhysicalRecovery.availableA N p) (M5.PhysicalRecovery.availableB N p) := by
        unfold M5.PhysicalRecovery.StateOK at hs
        unfold M5.ConditionalCount.PrefixOK
        aesop
      rw [M5.PhysicalRecovery.semantic_completion_count N w F hN hw hF hFN p hp hpa hpb]
      simpa [M5.PhysicalRecovery.oracle, M5.PhysicalRecovery.completionSet,
        hp, hs, hpa, hpb, hN, hw, hF, hFN, hOK, Nat.ne_of_gt hN, Nat.ne_of_gt hw]
        using M5.ConditionalCount.exact_completion_C N w F
          (M5.PhysicalRecovery.selectedA N p) (M5.PhysicalRecovery.selectedB N p)
          (M5.PhysicalRecovery.availableA N p) (M5.PhysicalRecovery.availableB N p)
          hN hF hFN hOK
    · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
        (Or.inr (Nat.lt_of_not_ge hpb))]
      simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC,
        hp, hs, hpa, hpb, hN, hw, hF, hFN]
  · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
      (Or.inl (Nat.lt_of_not_ge hpa))]
    simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC,
      hp, hs, hpa, hN, hw, hF, hFN]
