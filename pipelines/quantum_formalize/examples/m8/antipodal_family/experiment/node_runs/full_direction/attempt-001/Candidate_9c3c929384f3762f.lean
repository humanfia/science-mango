import FrozenTarget_9c3c929384f3762f
theorem M8.AntipodalFamily.full_direction : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  apply M8.CoverageFoundation.consecutive_full N (M8.AntipodalFamily.support N) 0
  · simp [M8.AntipodalFamily.support]
  · simp [M8.AntipodalFamily.support]
