import M7CanonicalBlock

theorem M7.CanonicalBlock.best_anchor_member : ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → M7.CanonicalBlock.bestAnchor A ∈ A := by
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

theorem M7.CanonicalBlock.decode_key : ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, M7.CanonicalBlock.decode N (M7.CanonicalBlock.key A) = A := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.decode N (M7.CanonicalBlock.key A) = A
  intro N inst A
  classical
  simp [M7.CanonicalBlock.decode, M7.CanonicalBlock.key, Finset.image_image]

theorem M7.CanonicalBlock.shift_add : ∀ (N : ℕ) [NeZero N], ∀ (s t : ZMod N) (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.shift s (M7.CanonicalBlock.shift t A) = M7.CanonicalBlock.shift (s+t) A := by
  intro N inst s t A
  classical
  simp only [M7.CanonicalBlock.shift, Finset.image_image, Function.comp_def, add_assoc, add_comm t s]

theorem M7.CanonicalBlock.shift_card : ∀ (N : ℕ) [NeZero N], ∀ (s : ZMod N) (A : M7.CanonicalBlock.Support N), (M7.CanonicalBlock.shift s A).card = A.card := by
  intro N inst s A
  classical
  change (A.image (fun i => i + s)).card = A.card
  apply Finset.card_image_of_injective
  intro a b h
  exact add_right_cancel h

theorem M7.CanonicalBlock.anchor_keys_shift : ∀ (N : ℕ) [NeZero N], ∀ (s : ZMod N) (A : M7.CanonicalBlock.Support N), (M7.CanonicalBlock.candidates (M7.CanonicalBlock.shift s A)).image (fun v => (ofLex v).1) = (M7.CanonicalBlock.candidates A).image (fun v => (ofLex v).1) := by
  intro N inst s A
  classical
  simp only [M7.CanonicalBlock.candidates, Finset.image_image]
  change (A.image (fun q => q + s)).image (fun q => M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) (M7.CanonicalBlock.shift s A))) = A.image (fun q => M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A))
  rw [Finset.image_image]
  apply Finset.image_congr
  intro q hq
  change M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-(q + s)) (M7.CanonicalBlock.shift s A)) = M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A)
  rw [M7.CanonicalBlock.shift_add]
  have h : -(q + s) + s = -q := by abel
  rw [h]

theorem M7.CanonicalBlock.key_injective : ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalBlock.key (N := N)) := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalBlock.key (N := N))
  intro N inst A B h
  have hd := congrArg (M7.CanonicalBlock.decode N) h
  rw [M7.CanonicalBlock.decode_key N A, M7.CanonicalBlock.decode_key N B] at hd
  exact hd

theorem M7.CanonicalBlock.normalize_minimal : ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → ∀ q ∈ A, M7.CanonicalBlock.key (M7.CanonicalBlock.normalize A) ≤ M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (s : ZMod N) (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.normalize (M7.CanonicalBlock.shift s A) = M7.CanonicalBlock.normalize A
