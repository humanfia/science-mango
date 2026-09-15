import FrozenTarget_de89e51b1fa04a2b
theorem M7.FinalReplay.invalid_rejection : QuantumHarnessFrozenTarget := by
  intro N w inst q hq c
  simp only [M7.FinalReplay.check, if_neg hq]
