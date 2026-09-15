import M7Presentation
import M7SelectionAccepted

theorem M7.Presentation.record_eta : ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a := by
  change ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a
  intro κ σ τ a
  rcases a with ⟨k, s, t⟩
  rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) (K : Finset κ) (S : Finset σ) (T : Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T ↔ M7.Presentation.outer a ∈ K ∧ M7.Presentation.left a ∈ S ∧ M7.Presentation.right a ∈ T
