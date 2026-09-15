import FrozenTarget_c367f1dc3291f082
theorem M7.Presentation.candidate_dominates : QuantumHarnessFrozenTarget := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a
  intro κ σ τ _ _ _ K L R a ha
  classical
  rcases ha with ⟨hk, hs, ht⟩
  have hL : (L (M7.Presentation.outer a)).Nonempty := ⟨M7.Presentation.left a, hs⟩
  have hR : (R (M7.Presentation.outer a)).Nonempty := ⟨M7.Presentation.right a, ht⟩
  refine ⟨M7.Presentation.mk (M7.Presentation.outer a) ((L _).min' hL) ((R _).min' hR), ?_, ?_⟩
  · unfold M7.Presentation.candidates
    first
    | solve
        apply Finset.mem_biUnion.mpr
        refine ⟨M7.Presentation.outer a, hk, ?_⟩
        simp [hL, hR]
    | solve
        apply Finset.mem_biUnion.mpr
        refine ⟨⟨M7.Presentation.outer a, hk⟩, Finset.mem_attach _ _, ?_⟩
        simp [hL, hR]
    | solve
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach]
        aesop
  · rw [← M7.Presentation.record_eta κ σ τ a]
    exact M7.Presentation.record_mono κ σ τ _ _ _ _ _
      (Finset.min'_le _ _ hs) (Finset.min'_le _ _ ht)
