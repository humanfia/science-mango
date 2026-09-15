import FrozenTarget_3ee96737f49ee6d8
theorem M6.ActualCounts.encoded_dimension : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  rw [M6.ActualCounts.boundary_finrank N a b ha hb,
    M6.ActualCounts.dual_boundary_finrank N a b ha hb]
  have hf := M6.ActualCounts.f_le_order N a b
  omega
