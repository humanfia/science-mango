import M7Presentation
import M7SelectionAccepted

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a
