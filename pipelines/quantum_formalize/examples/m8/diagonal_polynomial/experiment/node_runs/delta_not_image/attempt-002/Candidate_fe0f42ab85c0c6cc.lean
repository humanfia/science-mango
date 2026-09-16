import FrozenTarget_fe0f42ab85c0c6cc
theorem M8.DiagonalPolynomial.delta_not_image : QuantumHarnessFrozenTarget := by
  intro N inst p F hp hF hFne hFp hFM
  have hnot : ∀ h : M6.Physical.Block N,
      M6.Physical.conv N (M6.Coordinates.coefficients N p) h ≠ M6.Physical.delta N 0 := by
    intro h hh
    have he := congrArg (M6.Coordinates.encode N) hh
    rw [M6.Coordinates.encode_conv, M6.Coordinates.encode_polynomial N p hp,
      M8.DiagonalPolynomial.encode_delta N] at he
    apply hFne
    apply M8.DiagonalPolynomial.common_divisor_of_inverse N p F
      (M6.Coordinates.blockPolynomial N h) hF hFp hFM
    simpa only [M6.Coordinates.encode, M6.Cyclic.image] using he
  unfold M8.Diagonal.DeltaNotImage
  first
  | exact hnot
  | exact fun ⟨h, hh⟩ => hnot h hh
