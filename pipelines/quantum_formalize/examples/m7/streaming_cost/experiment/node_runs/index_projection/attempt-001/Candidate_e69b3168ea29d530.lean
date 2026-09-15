import FrozenTarget_e69b3168ea29d530
theorem M7.StreamingCost.index_projection : QuantumHarnessFrozenTarget := by
  change ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval, (M7.StreamingCost.allIndices H N p).result = M7.StreamingIndices.allIndices H N (fun x => (p x).result)
  intro H N inst p
  simp only [M7.StreamingCost.allIndices, M7.StreamingIndices.allIndices, M7.StreamingCost.allFin, M7.StreamingIndices.allFin, M7.StreamingCost.cursor_projection, M7.StreamingCost.record_projection]
