import FrozenTarget_6f33dfe8dbdbcdcc
theorem M6.ActualResult.Q_enumerator : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  unfold M6.ActualTransfer.Q
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = _
  rw [M6.ActualResult.cycle_normalized N a b h P, M6.ActualResult.boundary_normalized N a b h P]
  unfold M6.Spaces.logicalWords
  symm
  apply M6.Pinned.enumerator_sdiff <;> exact M6.Spaces.boundaries_are_cycles N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
