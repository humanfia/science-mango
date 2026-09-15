import FrozenTarget_0383a78409e52b8d
theorem M5.Signature.binary_dvd_antisymm : QuantumHarnessFrozenTarget := by
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
