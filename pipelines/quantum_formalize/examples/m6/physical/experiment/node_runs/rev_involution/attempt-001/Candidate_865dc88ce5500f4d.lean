import FrozenTarget_865dc88ce5500f4d
theorem M6.Physical.rev_involution : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a
  intro N a
  funext i
  simp only [M6.Physical.rev, neg_neg]
