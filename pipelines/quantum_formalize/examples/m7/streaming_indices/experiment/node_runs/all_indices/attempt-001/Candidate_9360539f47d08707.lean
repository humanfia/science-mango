import FrozenTarget_9360539f47d08707
theorem M7.StreamingIndices.all_indices : QuantumHarnessFrozenTarget := by
  change ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → Bool, M7.StreamingIndices.allIndices H N p = true ↔ ∀ x : M7.GlobalQuery.Index H N, p x = true
  intro H N inst p
  unfold M7.StreamingIndices.allIndices
  simp only [M7.StreamingIndices.all_fin, M7.StreamingIndices.all_records]
  constructor
  · intro h x
    rcases x with ⟨i, g⟩
    exact h i g
  · intro h i g
    exact h (i, g)
