import FrozenTarget_382b0a1c91e77b68
theorem M5.PhysicalRecovery.arithmetic_oracle_exact : QuantumHarnessFrozenTarget := by
  classical
  intro N w F hN hw hF hFN p hp
  by_cases hA : (M5.PhysicalRecovery.selectedA N p).card ≤ w
  · by_cases hB : (M5.PhysicalRecovery.selectedB N p).card ≤ w
    · have hs := M5.PhysicalRecovery.state_domains N p hN hp
      have hA0 : 0 ∈ M5.PhysicalRecovery.selectedA N p := by
        simp [M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selected]
      have hB0 : 0 ∈ M5.PhysicalRecovery.selectedB N p := by
        simp [M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.selected]
      have hOK : M5.ConditionalCount.PrefixOK N w
          (M5.PhysicalRecovery.selectedA N p)
          (M5.PhysicalRecovery.selectedB N p)
          (M5.PhysicalRecovery.availableA N p)
          (M5.PhysicalRecovery.availableB N p) := by
        unfold M5.PhysicalRecovery.StateOK at hs
        unfold M5.ConditionalCount.PrefixOK
        aesop
      rw [M5.PhysicalRecovery.semantic_completion_count N w F hN hw hF hFN p hp hA hB]
      exact M5.ConditionalCount.exact_completion_C N w F
        (M5.PhysicalRecovery.selectedA N p)
        (M5.PhysicalRecovery.selectedB N p)
        (M5.PhysicalRecovery.availableA N p)
        (M5.PhysicalRecovery.availableB N p) hN hF hFN hOK
    · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
          (Or.inr (Nat.lt_of_not_ge hB))]
      simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC, hA, hB]
  · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
        (Or.inl (Nat.lt_of_not_ge hA))]
    simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC, hA]
