import FrozenTarget_d153c49ff8f9f25c
theorem M6.Final.answer_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.AnswerCorrect N a b
  intro N inst a b h
  unfold M6.Final.AnswerCorrect
  have hs := @M6.ActualResult.solve_exact
  have hd := @M6.ActualCSS.common_quantum_distance
  have hp := @M6.Pinned.distance_spec
  have hj := @M6.ActualCSS.J_logical_iff
  have hw := @M6.Flatten.J_weight
  first
  | have hn := @M6.ActualCounts.logicals_nonempty_iff
    aesop
  | have hn := @M6.ActualResult.logicals_nonempty_iff
    aesop
