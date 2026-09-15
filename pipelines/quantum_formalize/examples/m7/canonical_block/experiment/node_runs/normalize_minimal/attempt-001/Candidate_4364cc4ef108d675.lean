import FrozenTarget_4364cc4ef108d675
theorem M7.CanonicalBlock.normalize_minimal : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → ∀ q ∈ A, _
  intro N inst A hA q hq
  have hq' : toLex (M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A), q.val) ∈ M7.CanonicalBlock.candidates A := by
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hc : (M7.CanonicalBlock.candidates A).Nonempty := ⟨_, hq'⟩
  have hm : M7.CanonicalBlock.bestKey A ≤ toLex (M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A), q.val) := by
    unfold M7.CanonicalBlock.bestKey
    rw [dif_pos hc]
    exact Finset.min'_le _ _ hq'
  rw [← M7.CanonicalBlock.best_key_agrees N A hA]
  exact Prod.Lex.monotone_fst _ _ hm
