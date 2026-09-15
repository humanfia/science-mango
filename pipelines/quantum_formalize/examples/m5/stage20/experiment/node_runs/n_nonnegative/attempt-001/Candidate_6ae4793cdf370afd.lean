import FrozenTarget_6ae4793cdf370afd
theorem M5.ArithmeticSubset.n_nonnegative : QuantumHarnessFrozenTarget := by
  intro P hP W k z
  classical
  rw [M5.ArithmeticSubset.n_exact P hP W k z]
  exact Int.natCast_nonneg _
