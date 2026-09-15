import FrozenTarget_7ecb6b6f572ee791
theorem M7.Presentation.factorLeast_none : QuantumHarnessFrozenTarget := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ), M7.Presentation.factorLeast K L R = none ↔ ¬ ∃ a : M7.Presentation.Record κ σ τ, M7.Presentation.valid K L R a
  intro κ σ τ _ _ _ K L R
  classical
  change M7.Presentation.leastOf (M7.Presentation.candidates K L R) = none ↔ _
  rw [(M7.Presentation.leastOf_spec (M7.Presentation.Record κ σ τ) (M7.Presentation.candidates K L R)).2]
  constructor
  · intro he ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := M7.Presentation.candidate_dominates κ σ τ K L R a ha
    simpa [he] using hb
  · intro h
    ext a
    constructor
    · intro ha
      exact False.elim (h ⟨a, M7.Presentation.candidates_sound κ σ τ K L R a ha⟩)
    · intro ha
      simp at ha
