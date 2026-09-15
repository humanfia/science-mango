import FrozenTarget_785e3b92b41e5ca0
theorem M5.PolynomialExclusion.cyclic_quotient_nonzero : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0
  intro F N hN hmonic hdvd hquot
  have hmul := EuclideanDomain.mul_div_cancel' hmonic.ne_zero hdvd
  have hzero : M5.cyclicModulus N = 0 := by
    rw [hquot, mul_zero] at hmul
    exact hmul.symm
  have hcoeff := congrArg (fun p : M5.BinaryPolynomial => p.coeff N) hzero
  simp [M5.cyclicModulus, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, Nat.ne_of_gt hN] at hcoeff
