import FrozenTarget_326529f2e8e4e671
theorem M5.PolynomialExclusion.cyclic_quotient_nonzero : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0
  intro F N hN hF hdvd hzero
  have hmod : M5.cyclicModulus N = 0 := by
    calc
      M5.cyclicModulus N = F * (M5.cyclicModulus N / F) :=
        (EuclideanDomain.mul_div_cancel' hdvd).symm
      _ = 0 := by rw [hzero, mul_zero]
  have hcoeff := congrArg (fun p : M5.BinaryPolynomial => p.coeff N) hmod
  simpa [M5.cyclicModulus, Polynomial.coeff_X_pow, Nat.ne_of_gt hN,
    Ne.symm (Nat.ne_of_gt hN)] using hcoeff
