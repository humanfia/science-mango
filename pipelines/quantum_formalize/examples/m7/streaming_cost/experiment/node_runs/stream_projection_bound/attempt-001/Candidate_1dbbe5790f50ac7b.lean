import FrozenTarget_1dbbe5790f50ac7b
theorem M7.StreamingCost.stream_projection_bound : QuantumHarnessFrozenTarget := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ x : M7.GlobalQuery.Index H N, _
  intro H N inst q bases x
  classical
  by_cases hx : M7.GlobalQuery.feasible q bases x
  · constructor
    · simp [M7.StreamingCost.streamWin, M7.StreamingIndices.streamWin, hx, M7.StreamingCost.index_projection]
    · have hb :
          (M7.StreamingCost.streamWin q bases x).outer ≤ (H * M7.StreamingCost.recordCount N) * 0 ∧
          (M7.StreamingCost.streamWin q bases x).inner ≤ (H * M7.StreamingCost.recordCount N) * 1 := by
        simp only [M7.StreamingCost.streamWin, if_pos hx]
        apply M7.StreamingCost.index_bound
        intro y
        dsimp
        split_ifs <;> simp
      simpa only [Nat.mul_zero, Nat.mul_one, Nat.le_zero] using hb
  · simp [M7.StreamingCost.streamWin, M7.StreamingIndices.streamWin, hx]
