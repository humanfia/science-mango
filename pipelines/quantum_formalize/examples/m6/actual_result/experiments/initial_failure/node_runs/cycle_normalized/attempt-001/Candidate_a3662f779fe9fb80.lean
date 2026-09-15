import FrozenTarget_a3662f779fe9fb80
theorem M6.ActualResult.cycle_normalized : QuantumHarnessFrozenTarget := by
  intro N inst a b h P
  rw [M6.ActualTransfer.character_trace_inputs N a b h P]
  first
  | rw [M6.ActualCounts.cycle_pinned_sum]
  | rw [M6.ActualResult.cycle_pinned_sum]
  | rw [M6.Spaces.cycle_pinned_sum]
  apply M6.Normalize.divide_scaled
  exact pow_ne_zero N (by norm_num)
