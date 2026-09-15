import FrozenTarget_0bb89a40aca623aa
theorem M6.Final.counting_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b
  intro N inst a b h
  rcases h with ⟨hN, ha0, hb0, hw, hs, hg⟩
  have hda : a.natDegree < N := by
    simpa [M6.ActualTransfer.span, max_lt_iff] using hs |>.1
  have hdb : b.natDegree < N := by
    simpa [M6.ActualTransfer.span, max_lt_iff] using hs |>.2
  have ha : a.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hda)
  have hb : b.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hdb)
  unfold M6.Final.CountingCorrect
  repeat' apply And.intro
  all_goals intros
  all_goals first
    | (rename_i P
       rw [M6.ActualTransfer.boundary_trace_inputs N a b hs P]
       change M6.ActualCounts.boundaryInputSum N a b P = _
       exact M6.ActualCounts.boundary_pinned_sum N a b ha hb P)
    | (rename_i P
       rw [M6.ActualTransfer.character_trace_inputs N a b hs P]
       change M6.ActualCounts.signedInputSum N a b P = _
       exact M6.ActualCounts.cycle_pinned_sum N a b ha hb P)
    | (exact?)
    | (simp only [M6.Final.LX, M6.Final.BX, M6.Final.CX]
       exact?)
