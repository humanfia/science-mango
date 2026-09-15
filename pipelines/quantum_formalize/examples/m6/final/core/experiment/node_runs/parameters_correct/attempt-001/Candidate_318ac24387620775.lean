import FrozenTarget_318ac24387620775
theorem M6.Final.parameters_correct : QuantumHarnessFrozenTarget := by
  intro N inst a b h
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have hna : a.natDegree < N := lt_of_le_of_lt (Nat.le_max_left _ _) hs
  have hnb : b.natDegree < N := lt_of_le_of_lt (Nat.le_max_right _ _) hs
  have ha : a.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hna)
  have hb : b.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnb)
  exact ⟨M6.ActualCounts.boundary_card N a b ha hb,
    M6.ActualCounts.cycle_card N a b ha hb,
    M6.ActualCounts.encoded_dimension N a b ha hb,
    M6.ActualCounts.f_le_order N a b,
    M6.ActualCounts.logicals_nonempty_iff N a b ha hb⟩
