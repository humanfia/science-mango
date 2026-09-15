import FrozenTarget_89c6a365b3539848
theorem M7.StreamingCost.scan_bound : QuantumHarnessFrozenTarget := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (M7.StreamingCost.scanWins q bases).outer ≤ H * M7.StreamingCost.recordCount N ∧ (M7.StreamingCost.scanWins q bases).inner ≤ (H * M7.StreamingCost.recordCount N)^2
  intro H N inst q bases
  classical
  have hb : ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval,
      (∀ x, (p x).outer ≤ 1 ∧ (p x).inner ≤ H * M7.StreamingCost.recordCount N) →
      (M7.StreamingCost.allIndices H N p).outer ≤ H * M7.StreamingCost.recordCount N ∧
      (M7.StreamingCost.allIndices H N p).inner ≤ (H * M7.StreamingCost.recordCount N)^2 := by
    intro p hp
    simpa only [Nat.mul_one, pow_two] using
      M7.StreamingCost.index_bound H N p 1 (H * M7.StreamingCost.recordCount N) hp
  unfold M7.StreamingCost.scanWins
  apply hb
  intro x
  have hs := M7.StreamingCost.stream_projection_bound H N q bases x
   dsimp only
  first | omega | (split <;> dsimp only <;> omega)
