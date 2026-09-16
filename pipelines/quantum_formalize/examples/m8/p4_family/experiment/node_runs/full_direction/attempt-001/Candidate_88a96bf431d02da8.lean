import FrozenTarget_88a96bf431d02da8
theorem M8.P4Family.full_direction : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.CoverageFoundation.FullDirection (M8.P4Family.support N)
  intro N inst hN
  apply M8.CoverageFoundation.consecutive_full N (M8.P4Family.support N) 0
  · exact (M8.P4Family.support_data N hN).2.1
  · simpa only [zero_add] using (M8.P4Family.support_data N hN).2.2
