import FrozenTarget_09a84da8813e1e71
theorem M8.WholeResources.charge_length : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6
  intro N _ c
  classical
  unfold M8.WholeResources.run
  split
  · norm_num
  · split
    · norm_num
    · split <;> norm_num
