import FrozenTarget_fa1d09fc9de9b635
theorem M6.ActualCSS.J_logical_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.CSS.logical (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) ↔ M6.Flatten.J N v ∈ M6.CSS.logical (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b))
  intro N inst a b v
  classical
  simp only [M6.CSS.logical, Finset.mem_sdiff, M6.ActualCSS.J_cycle_iff N a b v, M6.ActualCSS.J_boundary_iff N a b v]
