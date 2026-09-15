import M5Accepted

theorem M5.Signature.binary_monic : ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic := by
  change ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic
  intro P hP
  have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  change P.leadingCoeff = 1
  exact h P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP)

theorem M5.Signature.binary_dvd_antisymm : ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q := by
  change ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q
  intro P Q hPQ hQP
  by_cases hP : P = 0
  · subst P
    exact (zero_dvd_iff.mp hPQ).symm
  by_cases hQ : Q = 0
  · subst Q
    exact zero_dvd_iff.mp hQP
  exact Polynomial.eq_of_monic_of_associated
    (M5.Signature.binary_monic P hP)
    (M5.Signature.binary_monic Q hQ)
    (associated_of_dvd_dvd hPQ hQP)
