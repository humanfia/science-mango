import FrozenTarget_b68c28922dbfb677
theorem M6.Physical.J_weight : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Physical.wordWeight N (M6.Physical.J N z) = M6.Physical.wordWeight N z
  intro N inst z
  simp [M6.Physical.wordWeight, M6.Physical.J, M6.Physical.rev_weight, Nat.add_comm]
