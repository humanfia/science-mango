import FrozenTarget_c6b84c09163e4b82
theorem M7.CanonicalOuter.canonical_key_agrees : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c)
  intro N inst c
  have h := M7.CanonicalOuter.choices_nonempty N c
  have hb : M7.CanonicalOuter.best c ∈ M7.CanonicalOuter.choices c := by
    unfold M7.CanonicalOuter.best
    rw [dif_pos h]
    exact Finset.min'_mem _ _
  unfold M7.CanonicalOuter.choices at hb
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hb
  change (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.candidate c (ofLex (M7.CanonicalOuter.best c)).2)
  rw [← he]
  rfl
