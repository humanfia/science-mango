import FrozenTarget_15903e958d1bb26d
theorem M8.DiagonalPolynomial.distance_two : QuantumHarnessFrozenTarget := by
  intro N inst p F hp hdeg hF hFne hFp hFM
  exact M8.Diagonal.distance_two N (M6.Coordinates.coefficients N p)
    (M8.DiagonalPolynomial.coefficients_nonzero N p hp hdeg)
    (M8.DiagonalPolynomial.delta_not_image N p F hdeg hF hFne hFp hFM)
