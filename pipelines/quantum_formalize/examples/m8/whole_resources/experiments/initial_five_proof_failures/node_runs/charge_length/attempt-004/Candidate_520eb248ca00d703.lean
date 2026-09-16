import FrozenTarget_520eb248ca00d703
theorem M8.WholeResources.charge_length : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6
  intro N inst c
  classical
  unfold M8.WholeResources.run
  dsimp only
  split
  · simp
  · dsimp only
    split
    · simp
    · dsimp only
      split <;> simp
