import FrozenTarget_7721888f064b0b68
theorem M7.StreamingCost.index_bound : QuantumHarnessFrozenTarget := by
  intro H N inst p a b hp
  have h :
      (M7.StreamingCost.allIndices H N p).outer ≤ H * (M7.StreamingCost.recordCount N * a) ∧
      (M7.StreamingCost.allIndices H N p).inner ≤ H * (M7.StreamingCost.recordCount N * b) := by
    unfold M7.StreamingCost.allIndices M7.StreamingCost.allFin
    apply M7.StreamingCost.cursor_bound
    intro i
    apply M7.StreamingCost.record_bound
    intro g
    exact hp _
  simpa only [Nat.mul_assoc] using h
