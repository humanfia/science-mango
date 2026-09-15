import FrozenTarget_cd032ea1185e50f2
theorem M6.ActualCSS.zero_boundaries : QuantumHarnessFrozenTarget := by
  intro N _ a b
  classical
  constructor <;> simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords]
