import FrozenTarget_a82c5e7ec28e378f
theorem M7.CanonicalBlock.normalize_anchor : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → 0 ∈ M7.CanonicalBlock.normalize A
  intro N _ A hA
  classical
  unfold M7.CanonicalBlock.normalize M7.CanonicalBlock.shift
  apply Finset.mem_image.mpr
  exact ⟨M7.CanonicalBlock.bestAnchor A, M7.CanonicalBlock.best_anchor_member N A hA, by simp⟩
