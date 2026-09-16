import M8OrbitSpan

theorem M8.OrbitSpan.spans_nonempty : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → (M8.OrbitSpan.spans c).Nonempty := by
  classical
  intro N inst c hc₁ hc₂
  rcases hc₁ with ⟨a, ha⟩
  rcases hc₂ with ⟨b, hb⟩
  have hel : M8.Anchor.Eligible c false a b := by
    simpa [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right] using And.intro ha hb
  unfold M8.OrbitSpan.spans
  apply Finset.Nonempty.image
  refine ⟨M8.Anchor.record false 1 a b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simpa only [M8.Anchor.trial] using M8.Anchor.anchored N c false 1 a b hel

theorem M8.OrbitSpan.attained : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) = M8.OrbitSpan.value c := by
  classical
  intro N inst c hc₁ hc₂
  have hne := M8.OrbitSpan.spans_nonempty N c hc₁ hc₂
  have hm : M8.OrbitSpan.value c ∈ M8.OrbitSpan.spans c := by
    simpa [M8.OrbitSpan.value, hne] using Finset.min'_mem (M8.OrbitSpan.spans c) hne
  unfold M8.OrbitSpan.spans at hm
  rcases Finset.mem_image.mp hm with ⟨g, hg, heq⟩
  exact ⟨g, (Finset.mem_filter.mp hg).2, heq⟩

theorem M8.OrbitSpan.small_iff : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → ∀ L : ℕ, M8.OrbitSpan.value c ≤ L ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ L := by
  classical
  intro N inst c hc₁ hc₂ L
  have hn := M8.OrbitSpan.spans_nonempty N c hc₁ hc₂
  rw [M8.OrbitSpan.value, dif_pos hn]
  constructor
  · intro h
    have hm := Finset.min'_mem (M8.OrbitSpan.spans c) hn
    unfold M8.OrbitSpan.spans at hm
    rcases Finset.mem_image.mp hm with ⟨g, hg, heq⟩
    exact ⟨g, (Finset.mem_filter.mp hg).2, heq.trans_le h⟩
  · rintro ⟨g, hg, hL⟩
    have hm : M8.Anchor.span (M7.Action.act g c) ∈ M8.OrbitSpan.spans c := by
      unfold M8.OrbitSpan.spans
      exact Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩, rfl⟩
    exact le_trans (Finset.min'_le _ _ hm) hL

theorem M8.OrbitSpan.anchor_minimum : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → ∀ L : ℕ, M8.OrbitSpan.value c ≤ L ↔ ∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ L := by
  intro N inst c hc₁ hc₂ L
  exact (M8.OrbitSpan.small_iff N c hc₁ hc₂ L).trans (M8.Anchor.passing_presentations N c L).symm

theorem M8.OrbitSpan.less_than_order : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → M8.OrbitSpan.value c < N := by
  intro N inst c hc₁ hc₂
  rcases M8.OrbitSpan.attained N c hc₁ hc₂ with ⟨g, hg, heq⟩
  rw [← heq]
  exact M8.Anchor.span_lt_order N (M7.Action.act g c)
#print axioms M8.OrbitSpan.spans_nonempty
#print axioms M8.OrbitSpan.attained
#print axioms M8.OrbitSpan.less_than_order
#print axioms M8.OrbitSpan.small_iff
#print axioms M8.OrbitSpan.anchor_minimum
