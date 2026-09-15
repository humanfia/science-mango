import FrozenTarget_9d95438504d70e43
theorem M6.ActualResult.cycle_normalized : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  have ha : a.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_left a.natDegree b.natDegree) h : a.natDegree < N)
  have hb : b.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_right a.natDegree b.natDegree) h : b.natDegree < N)
  rw [M6.ActualTransfer.character_trace_inputs N a b h P]
  first
  | rw [← M6.ActualCounts.cycle_pinned_sum N a b ha hb P]
  | rw [← M6.ActualResult.cycle_pinned_sum N a b ha hb P]
  apply M6.Normalize.divide_scaled
  exact pow_ne_zero N (by norm_num)
