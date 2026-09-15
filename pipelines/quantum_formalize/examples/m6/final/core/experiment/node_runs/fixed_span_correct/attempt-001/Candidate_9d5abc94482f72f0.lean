import FrozenTarget_9d5abc94482f72f0
theorem M6.Final.fixed_span_correct : QuantumHarnessFrozenTarget := by
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
