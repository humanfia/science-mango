import FrozenTarget_0c145be5bced4234
theorem M8.MixedFamily.full_direction : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  apply M8.CoverageFoundation.consecutive_full N (M8.MixedFamily.left N) 0
  · simp [M8.MixedFamily.left]
  · simp [M8.MixedFamily.left]
