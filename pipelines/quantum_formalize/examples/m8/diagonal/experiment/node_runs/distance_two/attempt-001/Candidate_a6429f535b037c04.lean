import FrozenTarget_a6429f535b037c04
theorem M8.Diagonal.distance_two : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M6.Physical.Block N, p ≠ 0 → M8.Diagonal.DeltaNotImage N p → M8.Diagonal.distance N p = some 2
  intro N inst p hp hdelta
  unfold M8.Diagonal.distance
  rw [M6.ActualCSS.common_quantum_distance N p p]
  apply ((M6.Pinned.distance_spec (2 * N) (M6.Spaces.logicalWords N p p)).2 2).mpr
  constructor
  · exact ⟨M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0), M8.Diagonal.diagonal_witness N p hdelta⟩
  · intro v hv
    exact M8.Diagonal.logical_lower_bound N p v hp hv
