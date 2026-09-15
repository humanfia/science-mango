import FrozenTarget_02351a858117cc66
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
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualCounts.signedInputSum N a b P) = _
  rw [M6.ActualCounts.cycle_pinned_sum N a b ha hb P]
  exact M6.Normalize.divide_scaled _ _ (pow_ne_zero N (by norm_num))
