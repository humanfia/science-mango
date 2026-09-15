import FrozenTarget_89c7b9b1aa9957df
theorem M7.Presentation.record_eta : QuantumHarnessFrozenTarget := by
  change ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a
  intro κ σ τ a
  rcases a with ⟨k, s, t⟩
  rfl
