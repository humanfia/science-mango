import M7CanonicalBlock

theorem M7.CanonicalBlock.best_key_agrees : ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → (ofLex (M7.CanonicalBlock.bestKey A)).1 = M7.CanonicalBlock.key (M7.CanonicalBlock.normalize A) := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → _
  intro N inst A hA
  have hc : (M7.CanonicalBlock.candidates A).Nonempty := by
    rcases hA with ⟨q, hq⟩
    exact ⟨_, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have hm : M7.CanonicalBlock.bestKey A ∈ M7.CanonicalBlock.candidates A := by
    unfold M7.CanonicalBlock.bestKey
    rw [dif_pos hc]
    exact Finset.min'_mem _ hc
  change M7.CanonicalBlock.bestKey A ∈ A.image (fun q => toLex (M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A), q.val)) at hm
  rcases Finset.mem_image.mp hm with ⟨q, hq, heq⟩
  unfold M7.CanonicalBlock.normalize M7.CanonicalBlock.bestAnchor
  rw [← heq]
  simp
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → ∀ q ∈ A, M7.CanonicalBlock.key (M7.CanonicalBlock.normalize A) ≤ M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A)
