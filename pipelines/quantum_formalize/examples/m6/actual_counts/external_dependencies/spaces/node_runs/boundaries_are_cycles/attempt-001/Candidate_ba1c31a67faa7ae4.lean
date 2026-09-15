import FrozenTarget_ba1c31a67faa7ae4
theorem M6.Spaces.boundaries_are_cycles : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v hv
  obtain ⟨h, rfl⟩ := (M6.Spaces.boundary_words_iff N a b v).mp hv
  apply (M6.Spaces.cycle_words_iff N a b _).mpr
  rw [M6.Flatten.flatten_left]
  exact M6.Physical.boundary_cycle N a b h
