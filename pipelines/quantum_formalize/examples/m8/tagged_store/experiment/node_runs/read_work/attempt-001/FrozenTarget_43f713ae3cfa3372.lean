import M8TaggedStore

theorem M8.TaggedStore.comparison_exact : ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a=b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length+1 := by
  change ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a = b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length + 1
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp [M8.TaggedStore.compare]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [M8.TaggedStore.compare]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [M8.TaggedStore.compare] using ih ys
          · simp [M8.TaggedStore.compare, h]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.read key s).2 ≤ s.length*(4*(B+1))+1
