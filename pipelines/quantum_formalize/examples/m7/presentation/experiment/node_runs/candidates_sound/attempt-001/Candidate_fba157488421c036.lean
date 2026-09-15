import FrozenTarget_fba157488421c036
theorem M7.Presentation.candidates_sound : QuantumHarnessFrozenTarget := by
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
