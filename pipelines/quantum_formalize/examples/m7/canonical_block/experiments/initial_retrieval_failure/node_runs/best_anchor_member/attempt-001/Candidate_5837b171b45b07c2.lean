import FrozenTarget_5837b171b45b07c2
theorem M7.CanonicalBlock.best_anchor_member : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → M7.CanonicalBlock.bestAnchor A ∈ A
  intro N _ A hA
  classical
  have hc : (M7.CanonicalBlock.candidates A).Nonempty := by
    obtain ⟨q, hq⟩ := hA
    unfold M7.CanonicalBlock.candidates
    exact ⟨_, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have hk : M7.CanonicalBlock.bestKey A ∈ M7.CanonicalBlock.candidates A := by
    rw [M7.CanonicalBlock.bestKey, dif_pos hc]
    exact Finset.min'_mem _ _
  unfold M7.CanonicalBlock.candidates at hk
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hk
  unfold M7.CanonicalBlock.bestAnchor
  rw [← heq]
  simpa using hq
