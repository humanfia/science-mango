import FrozenTarget_526019c0b992cad7
theorem M6.ActualResult.Q_enumerator : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  unfold M6.ActualTransfer.Q
  rw [M6.ActualResult.cycle_normalized N a b h P,
    M6.ActualResult.boundary_normalized N a b h P]
  unfold M6.Spaces.logicalWords
  have hsub := M6.Spaces.boundaries_are_cycles N
    (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  first
  | solve
    | apply M6.Pinned.enumerator_sdiff
      exact hsub
  | solve
    | symm
      apply M6.Pinned.enumerator_sdiff
      exact hsub
