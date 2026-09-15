import FrozenTarget_d94a1227bd80e278
theorem M7.StreamingIndices.stream_winners : QuantumHarnessFrozenTarget := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.StreamingIndices.streamWin q bases x = true ↔ x ∈ M7.GlobalQuery.winners q bases
  classical
  intro H N inst q bases x
  unfold M7.StreamingIndices.streamWin
  simp only [Bool.and_eq_true, M7.StreamingIndices.all_indices, decide_eq_true_eq]
  exact ((M7.GlobalQuery.winners_exact H N q bases).1 x).symm
