import FrozenTarget_3a3db8051a886f2f
theorem M6.Final.counting_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b
  intro N inst a b h
  classical
  simp only [M6.Final.Admissible] at h
  have ha : a.degree < (N : WithBot ℕ) := by
    apply Polynomial.degree_lt_of_natDegree_lt
    first | omega | aesop | exact?
  have hb : b.degree < (N : WithBot ℕ) := by
    apply Polynomial.degree_lt_of_natDegree_lt
    first | omega | aesop | exact?
  unfold M6.Final.CountingCorrect
  repeat' constructor
  all_goals intros
  all_goals first
    | (rw [M6.ActualTransfer.boundary_trace_inputs N a b (by first | aesop | exact?)]
       change M6.ActualCounts.boundaryInputSum N a b _ = _
       exact M6.ActualCounts.boundary_pinned_sum N a b ha hb _)
    | (rw [M6.ActualTransfer.character_trace_inputs N a b (by first | aesop | exact?)]
       change M6.ActualCounts.signedInputSum N a b _ = _
       exact M6.ActualCounts.cycle_pinned_sum N a b ha hb _)
    | exact?
