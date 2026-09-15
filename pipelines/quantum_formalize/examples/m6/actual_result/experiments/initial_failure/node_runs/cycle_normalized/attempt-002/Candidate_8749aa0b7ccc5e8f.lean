import FrozenTarget_8749aa0b7ccc5e8f
theorem M6.ActualResult.cycle_normalized : QuantumHarnessFrozenTarget := by
  intro N inst a b h P
  rw [M6.ActualTransfer.character_trace_inputs N a b h P]
  first
  | rw [M6.ActualCounts.cycle_pinned_sum]
  | rw [← M6.ActualCounts.cycle_pinned_sum]
  all_goals first
  | exact M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))
  | exact h
  | exact lt_of_le_of_lt (show a.natDegree ≤ M6.ActualTransfer.span a b from Nat.le_max_left _ _) h
  | exact lt_of_le_of_lt (show b.natDegree ≤ M6.ActualTransfer.span a b from Nat.le_max_right _ _) h
  | exact Polynomial.degree_lt_of_natDegree_lt (lt_of_le_of_lt (show a.natDegree ≤ M6.ActualTransfer.span a b from Nat.le_max_left _ _) h)
  | exact Polynomial.degree_lt_of_natDegree_lt (lt_of_le_of_lt (show b.natDegree ≤ M6.ActualTransfer.span a b from Nat.le_max_right _ _) h)
