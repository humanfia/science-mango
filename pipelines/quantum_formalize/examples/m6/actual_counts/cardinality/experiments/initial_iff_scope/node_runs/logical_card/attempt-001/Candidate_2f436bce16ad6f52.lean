import FrozenTarget_2f436bce16ad6f52
theorem M6.ActualCounts.logical_card : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  classical
  have hsub := M6.Spaces.boundaries_are_cycles N
    (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  rw [M6.Spaces.logicalWords, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub),
    M6.ActualCounts.cycle_card N a b ha hb,
    M6.ActualCounts.boundary_card N a b ha hb]
  norm_cast
