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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) = M8.OrbitSpan.value c
