import M8DiagonalPolynomial

theorem M8.DiagonalPolynomial.coefficients_nonzero : ∀ (N : ℕ) [NeZero N], ∀ p : M8.DiagonalPolynomial.BP, p ≠ 0 → p.degree < (N : WithBot ℕ) → M6.Coordinates.coefficients N p ≠ 0 := by
  intro N inst p hp hdeg hzero
  apply hp
  have hrec := M6.Coordinates.block_reconstruct N p hdeg
  rw [hzero] at hrec
  simpa [M6.Coordinates.blockPolynomial] using hrec.symm

theorem M8.DiagonalPolynomial.common_divisor_of_inverse : ∀ (N : ℕ) [NeZero N], ∀ (p F q : M8.DiagonalPolynomial.BP), F.Monic → F ∣ p → F ∣ M6.Cyclic.modulus N → M6.Cyclic.image N p * M6.Cyclic.image N q = 1 → F = 1 := by
  intro N inst p F q hF hFp hFM hInv
  change AdjoinRoot.mk (M6.Cyclic.modulus N) p * AdjoinRoot.mk (M6.Cyclic.modulus N) q = 1 at hInv
  have hm : AdjoinRoot.mk (M6.Cyclic.modulus N) (p * q) = AdjoinRoot.mk (M6.Cyclic.modulus N) 1 := by
    simpa only [map_mul, map_one] using hInv
  rw [AdjoinRoot.mk_eq_mk] at hm
  have hpq : F ∣ p * q := dvd_mul_of_dvd_left hFp q
  have hsub : F ∣ p * q - 1 := dvd_trans hFM hm
  have h1 : F ∣ 1 := by
    have h := dvd_sub hpq hsub
    simpa only [sub_sub_cancel] using h
  first
  | exact hF.eq_one_of_dvd_one h1
  | exact hF.isUnit_iff.mp (isUnit_of_dvd_one h1)
  | exact hF.dvd_antisymm Polynomial.monic_one h1 (one_dvd F)

theorem M8.DiagonalPolynomial.encode_delta : ∀ (N : ℕ) [NeZero N], M6.Coordinates.encode N (M6.Physical.delta N 0) = 1 := by
  intro N inst
  rw [M6.Coordinates.encode_sum]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [M6.Physical.delta, M6.Coordinates.rootPow]
  · intro i hi hne
    simp [M6.Physical.delta, hne, Ne.symm hne]
  · simp

theorem M8.DiagonalPolynomial.delta_not_image : ∀ (N : ℕ) [NeZero N], ∀ (p F : M8.DiagonalPolynomial.BP), p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ M6.Cyclic.modulus N → M8.Diagonal.DeltaNotImage N (M6.Coordinates.coefficients N p) := by
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

theorem M8.DiagonalPolynomial.distance_two : ∀ (N : ℕ) [NeZero N], ∀ (p F : M8.DiagonalPolynomial.BP), p ≠ 0 → p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ M6.Cyclic.modulus N → M8.Diagonal.distance N (M6.Coordinates.coefficients N p) = some 2 := by
  intro N inst p F hp hdeg hF hFne hFp hFM
  exact M8.Diagonal.distance_two N (M6.Coordinates.coefficients N p)
    (M8.DiagonalPolynomial.coefficients_nonzero N p hp hdeg)
    (M8.DiagonalPolynomial.delta_not_image N p F hdeg hF hFne hFp hFM)
#print axioms M8.DiagonalPolynomial.coefficients_nonzero
#print axioms M8.DiagonalPolynomial.common_divisor_of_inverse
#print axioms M8.DiagonalPolynomial.encode_delta
#print axioms M8.DiagonalPolynomial.delta_not_image
#print axioms M8.DiagonalPolynomial.distance_two
