import FrozenTarget_341c119a1349e348
theorem M6.Physical.boundary_cycle : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0
  intro N inst a b h
  dsimp only [M6.Physical.syndrome, M6.Physical.boundary]
  simp only [M6.Physical.conv_assoc, M6.Physical.conv_comm N b a]
  funext i
  exact ZModModule.add_self (G := ZMod 2) _
