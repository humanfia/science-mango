import FrozenTarget_8b3cf2797647dfd9
theorem M7.Presentation.domain_membership : QuantumHarnessFrozenTarget := by
  change ∀ (κ σ τ : Type) (K : Finset κ) (S : Finset σ) (T : Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T ↔ M7.Presentation.outer a ∈ K ∧ M7.Presentation.left a ∈ S ∧ M7.Presentation.right a ∈ T
  classical
  intro κ σ τ K S T a
  rcases a with ⟨k, s, t⟩
  simp [M7.Presentation.domain, M7.Presentation.mk, M7.Presentation.outer, M7.Presentation.left, M7.Presentation.right, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
