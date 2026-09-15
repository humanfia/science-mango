import FrozenTarget_98a6945168067614
theorem M6.Final.counting_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b
  intro N inst a b h
  classical
  simp only [M6.Final.Admissible] at h
  repeat' match goal with
    | h' : _ ∧ _ ⊢ _ => rcases h' with ⟨hleft, hright⟩
  have hs : M6.ActualTransfer.span a b < N := by assumption
  have hna : a.natDegree < N := by
    unfold M6.ActualTransfer.span at hs
    omega
  have hnb : b.natDegree < N := by
    unfold M6.ActualTransfer.span at hs
    omega
  have ha : a.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hna)
  have hb : b.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnb)
  unfold M6.Final.CountingCorrect
  repeat' apply And.intro
  all_goals intros
  all_goals first
    | (rw [M6.ActualTransfer.boundary_trace_inputs N a b hs]
       change M6.ActualCounts.boundaryInputSum N a b _ = _
       exact M6.ActualCounts.boundary_pinned_sum N a b ha hb _)
    | (rw [M6.ActualTransfer.character_trace_inputs N a b hs]
       change M6.ActualCounts.signedInputSum N a b _ = _
       exact M6.ActualCounts.cycle_pinned_sum N a b ha hb _)
    | exact?
    | (simp only [M6.Final.LX, M6.Final.BX, M6.Final.CX]
       exact?)
    | (rw [← M6.ActualCounts.logical_card N a b ha hb]
       exact?)
