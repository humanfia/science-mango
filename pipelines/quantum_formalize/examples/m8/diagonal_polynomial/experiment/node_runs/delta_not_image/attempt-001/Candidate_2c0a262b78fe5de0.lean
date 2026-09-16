import FrozenTarget_2c0a262b78fe5de0
theorem M8.DiagonalPolynomial.delta_not_image : QuantumHarnessFrozenTarget := by
  intro N inst p F hp hF hFne hFp hFM
  unfold M8.Diagonal.DeltaNotImage
  first
  | intro h hh
  | rintro ⟨h, hh⟩
  have he := congrArg (M6.Coordinates.encode N) hh
  rw [M6.Coordinates.encode_conv, M6.Coordinates.encode_polynomial N p hp,
    M8.DiagonalPolynomial.encode_delta N] at he
  apply hFne
  apply M8.DiagonalPolynomial.common_divisor_of_inverse N p F
    (M6.Coordinates.blockPolynomial N h) hF hFp hFM
  simpa only [M6.Coordinates.encode] using he
