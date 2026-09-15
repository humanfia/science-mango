import FrozenTarget_738391738c169150
theorem M6.ActualResult.Q_zero : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  rw [M6.ActualResult.Q_enumerator N a b h P]
  apply M6.Pinned.enumerator_zero_coeff
  exact M6.Spaces.zero_not_logical N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
