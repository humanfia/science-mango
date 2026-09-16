import FrozenTarget_82e4f9194ba64ac8
theorem M8.WholeResources.charge_length : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6
  intro N _ c
  classical
  unfold M8.WholeResources.run
  dsimp only
  split
  · norm_num
  · dsimp only
    split
    · norm_num [List.length_append]
    · dsimp only
      split <;> norm_num [List.length_append]
