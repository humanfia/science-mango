import FrozenTarget_b9fabae2551196e9
theorem M5.SupportPolynomial.quotient_monomial_period : QuantumHarnessFrozenTarget := by
  intro T a j
  let q := AdjoinRoot.mk (M5.cyclicModulus T)
  have htwo : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    ext n
    by_cases h : n = 0 <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_one, h]
  have hone : (1 : AdjoinRoot (M5.cyclicModulus T)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg q htwo
  have hsum : q ((Polynomial.X : M5.BinaryPolynomial) ^ T) + 1 = 0 := by
    have h := AdjoinRoot.mk_self (M5.cyclicModulus T)
    change q ((Polynomial.X : M5.BinaryPolynomial) ^ T + 1) = 0 at h
    simpa only [map_add, map_one] using h
  have hp : q ((Polynomial.X : M5.BinaryPolynomial) ^ T) = 1 :=
    add_right_cancel (hsum.trans hone.symm)
  change q ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) =
    q ((Polynomial.X : M5.BinaryPolynomial) ^ a)
  simp only [map_pow] at hp ⊢
  rw [pow_add, Nat.mul_comm j T, pow_mul, hp, one_pow, mul_one]
