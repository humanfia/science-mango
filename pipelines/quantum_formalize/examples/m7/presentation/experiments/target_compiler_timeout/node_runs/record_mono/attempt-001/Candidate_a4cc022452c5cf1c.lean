import FrozenTarget_a4cc022452c5cf1c
theorem M7.Presentation.record_mono : QuantumHarnessFrozenTarget := by
  intro κ σ τ _ _ _ k s s1 t t1 hs ht
  rcases lt_or_eq_of_le hs with h | h
  · simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, h, le_of_lt h, not_le_of_gt h, ht]
  · subst s1
    simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, ht]
