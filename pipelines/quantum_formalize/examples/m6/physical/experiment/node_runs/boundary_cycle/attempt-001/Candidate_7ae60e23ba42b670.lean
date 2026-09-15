import FrozenTarget_7ae60e23ba42b670
theorem M6.Physical.boundary_cycle : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0
  intro N inst a b h
  simp only [M6.Physical.syndrome, M6.Physical.boundary, M6.Physical.conv_assoc, M6.Physical.conv_comm N b a]
  funext i
  exact ZModModule.add_self _
