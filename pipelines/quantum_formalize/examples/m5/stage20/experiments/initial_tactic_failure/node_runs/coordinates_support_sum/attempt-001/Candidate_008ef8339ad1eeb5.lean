import FrozenTarget_008ef8339ad1eeb5
theorem M5.ArithmeticSubset.coordinates_support_sum : QuantumHarnessFrozenTarget := by
  intro P hP U
  classical
  simp [M5.SupportPolynomial.ofSupport, M5.SubsetCharacter.vectorSum,
    M5.QuotientCharacter.coordinates, map_sum, Finset.sum_apply]
