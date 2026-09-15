import FrozenTarget_cd0016d6d0e1467c
theorem M5.Period.period_one : QuantumHarnessFrozenTarget := by
  change M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1
  apply Nat.dvd_one.mp
  exact ((M5.Period.period_law (1 : M5.BinaryPolynomial)
    Polynomial.monic_one (by simp)).2 1).mp (one_dvd _)
