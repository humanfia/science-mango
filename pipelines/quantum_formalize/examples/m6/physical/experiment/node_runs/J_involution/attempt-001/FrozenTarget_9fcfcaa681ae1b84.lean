import M6Physical

theorem M6.Physical.rev_involution : ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a := by
  change ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a
  intro N a
  funext i
  simp only [M6.Physical.rev, neg_neg]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (z : M6.Physical.Word N), M6.Physical.J N (M6.Physical.J N z) = z
