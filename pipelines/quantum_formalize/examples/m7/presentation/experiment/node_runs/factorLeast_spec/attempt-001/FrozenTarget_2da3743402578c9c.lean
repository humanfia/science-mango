import M7Presentation
import M7SelectionAccepted

theorem M7.Presentation.candidates_sound : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.candidates K L R → M7.Presentation.valid K L R a := by
  classical
  intro κ σ τ _ _ _ K L R a ha
  unfold M7.Presentation.candidates at ha
  rcases Finset.mem_biUnion.mp ha with ⟨k, hk, ha⟩
  split at ha
  · have heq := Finset.mem_singleton.mp ha
    subst a
    simp [M7.Presentation.valid, M7.Presentation.outer,
      M7.Presentation.left, M7.Presentation.right,
      M7.Presentation.mk, hk, Finset.min'_mem]
  · simp at ha

theorem M7.Presentation.leastOf_spec : ∀ (α : Type) [LinearOrder α] (T : Finset α), (∀ x, M7.Presentation.leastOf T = some x ↔ x ∈ T ∧ ∀ y ∈ T, x ≤ y) ∧ (M7.Presentation.leastOf T = none ↔ T = ∅) := by
  classical
  intro α inst T
  by_cases h : T.Nonempty
  · constructor
    · intro x
      simp only [M7.Presentation.leastOf, dif_pos h, Option.some.injEq]
      constructor
      · intro hx
        rw [← hx]
        exact ⟨Finset.min'_mem T h, fun y hy => Finset.min'_le T y hy⟩
      · rintro ⟨hx, hmin⟩
        exact le_antisymm (Finset.min'_le T x hx) (hmin _ (Finset.min'_mem T h))
    · simp [M7.Presentation.leastOf, h, h.ne_empty]
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    simp [M7.Presentation.leastOf]

theorem M7.Presentation.record_eta : ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a := by
  change ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a
  intro κ σ τ a
  rcases a with ⟨k, s, t⟩
  rfl

theorem M7.Presentation.record_mono : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (k : κ) (s s1 : σ) (t t1 : τ), s ≤ s1 → t ≤ t1 → M7.Presentation.mk k s t ≤ M7.Presentation.mk k s1 t1 := by
  intro κ σ τ _ _ _ k s s1 t t1 hs ht
  rcases lt_or_eq_of_le hs with h | h
  · simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, h, le_of_lt h, not_le_of_gt h, ht]
  · subst s1
    simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, ht]

theorem M7.Presentation.candidate_dominates : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a
  intro κ σ τ _ _ _ K L R a ha
  classical
  rcases ha with ⟨hk, hs, ht⟩
  have hL : (L (M7.Presentation.outer a)).Nonempty := ⟨_, hs⟩
  have hR : (R (M7.Presentation.outer a)).Nonempty := ⟨_, ht⟩
  refine ⟨M7.Presentation.mk (M7.Presentation.outer a) ((L (M7.Presentation.outer a)).min' hL) ((R (M7.Presentation.outer a)).min' hR), ?_, ?_⟩
  · unfold M7.Presentation.candidates
    apply Finset.mem_biUnion.mpr
    refine ⟨M7.Presentation.outer a, hk, ?_⟩
    simp [hL, hR]
  · simpa only [M7.Presentation.record_eta] using
      (M7.Presentation.record_mono κ σ τ (M7.Presentation.outer a)
        ((L (M7.Presentation.outer a)).min' hL) (M7.Presentation.left a)
        ((R (M7.Presentation.outer a)).min' hR) (M7.Presentation.right a)
        (Finset.min'_le _ _ hs) (Finset.min'_le _ _ ht))
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.factorLeast K L R = some a ↔ M7.Presentation.valid K L R a ∧ ∀ b, M7.Presentation.valid K L R b → a ≤ b
