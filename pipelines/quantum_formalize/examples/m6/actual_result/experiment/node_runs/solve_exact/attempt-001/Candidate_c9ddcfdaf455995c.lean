import FrozenTarget_c9ddcfdaf455995c
theorem M6.ActualResult.solve_exact : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  exact M6.Pinned.solve_exact (2 * N)
    (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a)
      (M6.Coordinates.coefficients N b))
    (M6.ActualTransfer.Q N a b)
    (M6.ActualResult.Q_enumerator N a b h)
