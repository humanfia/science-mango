import M5SupportPolynomial

theorem M5.SupportPolynomial.quotient_monomial_period : ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a) := by
  change ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a)
  intro T a j
  let q := AdjoinRoot.mk (M5.cyclicModulus T)
  have htwo : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [map_add, Polynomial.C_1, map_zero] using congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) h
  have htwoq : (1 : AdjoinRoot (M5.cyclicModulus T)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg q htwo
  have hmod : q ((Polynomial.X : M5.BinaryPolynomial) ^ T + 1) = 0 := by
    change AdjoinRoot.mk (M5.cyclicModulus T) (M5.cyclicModulus T) = 0
    exact AdjoinRoot.mk_self
  have hsum : q Polynomial.X ^ T + 1 = 0 := by
    simpa only [map_add, map_pow, map_one] using hmod
  have hpow : q Polynomial.X ^ T = 1 := by
    apply add_right_cancel (b := (1 : AdjoinRoot (M5.cyclicModulus T)))
    exact hsum.trans htwoq.symm
  change q (Polynomial.X ^ (a + j * T)) = q (Polynomial.X ^ a)
  rw [map_pow, map_pow, pow_add, Nat.mul_comm j T, pow_mul, hpow, one_pow, mul_one]
