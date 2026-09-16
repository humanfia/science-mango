import FrozenTarget_5b234b31c6139d02
theorem M8.DiagonalPolynomial.encode_delta : QuantumHarnessFrozenTarget := by
  intro N inst
  rw [M6.Coordinates.encode_sum]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [M6.Physical.delta, M6.Coordinates.rootPow]
  · intro i hi hne
    simp [M6.Physical.delta, hne, Ne.symm hne]
  · simp
