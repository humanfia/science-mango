import FrozenTarget_34520eeac3c54886
theorem M8.WholeResources.charge_length : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6
  intro N inst c
  classical
  unfold M8.WholeResources.run
  split
  · norm_num only [List.length_append, List.length_cons, List.length_nil]
  · split
    · norm_num only [List.length_append, List.length_cons, List.length_nil]
    · split <;> norm_num only [List.length_append, List.length_cons, List.length_nil]
