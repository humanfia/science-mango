import FrozenTarget_e34870d1591f5365
theorem M5.ArithmeticTuple.tuple_coordinates : QuantumHarnessFrozenTarget := by
  intro P hP T d k t
  classical
  simp [M5.ArithmeticTuple.tuplePolynomial, M5.TupleCharacter.vectorSum,
    M5.QuotientCharacter.coordinates, map_sum]
