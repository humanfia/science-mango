import FrozenTarget_2b0f48484e195ba2
theorem M7.DefaultQuery.invalid_rejection : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst q base
  constructor
  · intro hInvalid
    constructor
    · simp [M7.DefaultQuery.answer, hInvalid]
    · apply (M7.DefaultQuery.winners_exact N q base).2.mpr
      rintro ⟨g, hg⟩
      exact hInvalid hg.1
  · intro hValid
    simp [M7.DefaultQuery.answer, hValid]
