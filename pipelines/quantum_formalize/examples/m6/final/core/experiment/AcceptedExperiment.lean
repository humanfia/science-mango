import M6FinalReady

theorem M6.Final.answer_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.AnswerCorrect N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.AnswerCorrect N a b
  intro N inst a b h
  classical
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have ha : a.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_left a.natDegree b.natDegree) hs)
  have hb : b.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_right a.natDegree b.natDegree) hs)
  have solve := M6.ActualResult.solve_exact N a b hs
  have nonempty := M6.ActualCounts.logicals_nonempty_iff N a b ha hb
  have empty : M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) = ∅ ↔ M6.ActualCounts.f N a b = 0 := by
    rw [← Finset.not_nonempty_iff_eq_empty, nonempty]
    omega
  have qd : M6.Final.quantumDistance N a b = M6.Pinned.distance (M6.Final.LX N a b) := M6.ActualCSS.common_quantum_distance N _ _
  have ds := M6.Pinned.distance_spec (2*N) (M6.Final.LX N a b)
  change (_ ↔ _) ∧ (_ ↔ _) ∧ _
  refine ⟨solve.1.trans empty, ?_, ?_, ?_⟩
  · rw [qd, ds.1]; exact empty
  · intro d v k hv
    have hvp := solve.2 d v k hv
    refine ⟨?_, hvp.1, hvp.2.1, ?_, (M6.Flatten.J_weight N v).trans hvp.2.1, hvp.2.2.2⟩
    · rw [qd, ds.2 d]
      exact ⟨⟨v, hvp.1, hvp.2.1⟩, hvp.2.2.1⟩
    · exact (M6.ActualCSS.J_logical_iff N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) v).mp hvp.1
  · intro hf
    cases hh : M6.ActualTransfer.solve N a b with
    | none => have hz := (solve.1.trans empty).mp hh; omega
    | some x => rcases x with ⟨d,v,k⟩; exact ⟨d,v,k,rfl⟩

theorem M6.Final.counting_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b := by
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

theorem M6.Final.execution_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b
  intro N inst a b h
  have hb := M6.ActualTransfer.boundary_indexed_resources
  have hc := M6.ActualTransfer.character_indexed_resources
  have ho := M6.ActualTransfer.shifted_output_exact
  have hs := M6.ActualTransfer.shifted_scan_exact
  first
  | have hd := M6.SolveResources.actual_distance_work
  | have hd := M6.Solve.actual_distance_work
  | have hd := M6.QueryResources.actual_distance_work
  | have hd := M6.Query.actual_distance_work
  | have hd := M6.Postprocessing.actual_distance_work
  | have hd := M6.ActualTransfer.actual_distance_work
  | have hd := M6.Final.actual_distance_work
  | have hd := M6.actual_distance_work
  first
  | have hw := M6.SolveResources.actual_witness_work
  | have hw := M6.Solve.actual_witness_work
  | have hw := M6.QueryResources.actual_witness_work
  | have hw := M6.Query.actual_witness_work
  | have hw := M6.Postprocessing.actual_witness_work
  | have hw := M6.ActualTransfer.actual_witness_work
  | have hw := M6.Final.actual_witness_work
  | have hw := M6.actual_witness_work
  unfold M6.Final.Admissible at h
  unfold M6.Final.ExecutionCorrect
  aesop (add safe apply [hb, hc, ho, hs, hd, hw])

theorem M6.Final.fixed_span_correct : M6.Final.FixedSpanCorrect := by
  change M6.Final.FixedSpanCorrect
  refine ⟨M6.FixedSpan.distance_improvement, M6.FixedSpan.witness_improvement, ?_⟩
  intro k
  have h := M6.FixedSpan.nontrivial_family k
  have hd := M6.FixedSpan.recipe_degree.2
  have hs : M6.ActualTransfer.span M6.FixedSpan.recipe M6.FixedSpan.recipe = 2 := by
    simp [M6.ActualTransfer.span, hd]
  refine ⟨?_, hs, h.2.2.2.2⟩
  change 0 < 3*(k+1) ∧ _
  refine ⟨by omega, ?_, ?_, rfl, ?_, ?_⟩
  · simp [M6.FixedSpan.recipe]
  · simp [M6.FixedSpan.recipe]
  · rw [hs]; exact h.1
  · simpa only [Finset.union_self] using h.2.2.2.1

theorem M6.Final.parameters_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ParametersCorrect N a b := by
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

theorem M6.Final.zero_span_correct : M6.Final.ZeroSpanCorrect := by
  change M6.Final.ZeroSpanCorrect
  refine ⟨M6.ZeroSpan.anchored_zero, M6.ZeroSpan.connected_zero, M6.ZeroSpan.boundary_loops, M6.ZeroSpan.character_loops, M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero, ?_⟩
  intro N inst
  unfold M6.ActualTransfer.Q
  rw [M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero]
  have hf : M6.ActualCounts.f N 1 1 = 0 := by
    unfold M6.ActualCounts.f
    rw [M6.ZeroSpan.signature_one]
    simp
  change M6.Normalize.divide ((2 : ℤ)^N) (Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N 1 1)) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) = 0
  rw [hf]
  simp only [pow_zero]
  rw [M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))]
  have h1 := M6.Normalize.divide_scaled (1 : ℤ) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) (by norm_num)
  simp only [map_one, one_mul] at h1
  rw [h1]
  exact sub_self _
#print axioms M6.Final.answer_correct
#print axioms M6.Final.counting_correct
#print axioms M6.Final.execution_correct
#print axioms M6.Final.fixed_span_correct
#print axioms M6.Final.parameters_correct
#print axioms M6.Final.zero_span_correct
