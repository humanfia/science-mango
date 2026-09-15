import FrozenTarget_850fb81b36cfa662
theorem M6.Flatten.J_involution : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.J N (M6.Flatten.J N v) = v
  intro N inst v
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_left, M6.Physical.J_involution, M6.Flatten.flatten_right]
