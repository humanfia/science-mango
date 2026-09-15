import FrozenTarget_39445ebfa6dc2ae3
theorem M6.Pinned.count_nonnegative_positive : QuantumHarnessFrozenTarget := by
  classical
  intro m L P d
  unfold M6.Pinned.count
  constructor
  · exact Int.natCast_nonneg _
  · simp [Int.natCast_pos, Finset.card_pos, Finset.Nonempty, and_assoc]
