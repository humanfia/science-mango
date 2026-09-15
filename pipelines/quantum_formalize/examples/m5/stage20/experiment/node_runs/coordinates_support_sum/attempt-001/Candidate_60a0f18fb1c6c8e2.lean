import FrozenTarget_60a0f18fb1c6c8e2
theorem M5.ArithmeticSubset.coordinates_support_sum : QuantumHarnessFrozenTarget := by
  intro P hP U
  classical
  simp [M5.SupportPolynomial.ofSupport, M5.SubsetCharacter.vectorSum,
    M5.QuotientCharacter.coordinates, map_sum, Finset.sum_apply]
