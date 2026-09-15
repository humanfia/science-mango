import FrozenTarget_16c1c1fb91f208d6
theorem M6.ActualCSS.zero_boundaries : QuantumHarnessFrozenTarget := by
  intro N _ a b
  classical
  constructor <;> simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords]
