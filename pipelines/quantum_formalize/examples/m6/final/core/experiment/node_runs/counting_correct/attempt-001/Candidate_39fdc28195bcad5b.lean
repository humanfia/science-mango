import FrozenTarget_39fdc28195bcad5b
theorem M6.Final.counting_correct : QuantumHarnessFrozenTarget := by
  intro N inst a b h
  classical
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have hna : a.natDegree < N := lt_of_le_of_lt (Nat.le_max_left _ _) hs
  have hnb : b.natDegree < N := lt_of_le_of_lt (Nat.le_max_right _ _) hs
  have ha : a.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hna)
  have hb : b.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnb)
  constructor
  · intro P
    refine ⟨?_, ?_, M6.ActualResult.boundary_normalized N a b hs P,
      M6.ActualResult.cycle_normalized N a b hs P,
      M6.ActualResult.Q_enumerator N a b hs P,
      (fun d => M6.ActualResult.Q_coeff N a b hs P d),
      M6.ActualResult.Q_zero N a b hs P⟩
    · rw [M6.ActualTransfer.boundary_trace_inputs N a b hs P]
      simpa only [M6.ActualCounts.boundaryInputSum, M6.Spaces.boundary_eval, M6.Final.BX] using
        M6.ActualCounts.boundary_pinned_sum N a b ha hb P
    · rw [M6.ActualTransfer.character_trace_inputs N a b hs P]
      simpa only [M6.ActualCounts.signedInputSum, M6.Spaces.dual_boundary_eval, M6.Final.CX] using
        M6.ActualCounts.cycle_pinned_sum N a b ha hb P
  · exact (M6.ActualResult.Q_total N a b hs).trans (M6.ActualCounts.logical_card N a b ha hb)
