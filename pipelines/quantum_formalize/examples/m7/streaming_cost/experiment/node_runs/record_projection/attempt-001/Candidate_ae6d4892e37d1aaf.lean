import FrozenTarget_ae6d4892e37d1aaf
theorem M7.StreamingCost.record_projection : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → M7.StreamingCost.Eval, (M7.StreamingCost.allRecords N p).result = M7.StreamingIndices.allRecords N (fun g => (p g).result)
  intro N inst p
  simp only [M7.StreamingCost.allRecords, M7.StreamingIndices.allRecords, M7.StreamingCost.allFin, M7.StreamingIndices.allFin, M7.StreamingCost.cursor_projection]
