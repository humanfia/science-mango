import FrozenTarget_4dd40ab2c64941b4
theorem M7.GlobalQuery.invalid_rejection : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases
  constructor
  · intro hbad
    constructor
    · simp [M7.GlobalQuery.answer, hbad]
    · apply (M7.GlobalQuery.winners_exact H N q bases).2.mpr
      rintro ⟨x, hx⟩
      simpa [M7.GlobalQuery.feasible, M7.DefaultQuery.feasible, hbad] using hx
  · intro hvalid
    simp [M7.GlobalQuery.answer, hvalid]
