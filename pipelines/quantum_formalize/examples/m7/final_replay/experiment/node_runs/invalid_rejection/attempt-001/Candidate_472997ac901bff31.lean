import FrozenTarget_472997ac901bff31
theorem M7.FinalReplay.invalid_rejection : QuantumHarnessFrozenTarget := by
  intro N w inst q hq c
  simp only [M7.FinalReplay.check, if_neg hq]
