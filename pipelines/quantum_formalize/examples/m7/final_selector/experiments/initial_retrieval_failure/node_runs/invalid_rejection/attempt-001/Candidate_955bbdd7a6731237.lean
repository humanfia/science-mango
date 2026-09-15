import FrozenTarget_955bbdd7a6731237
theorem M7.FinalSelector.invalid_rejection : QuantumHarnessFrozenTarget := by
  intro N w inst q h
  constructor
  · intro x
    simp [M7.FinalSelector.answer, h]
  · simp [M7.FinalSelector.RawFeasible, M7.DefaultQuery.feasible, h]
