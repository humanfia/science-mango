import FrozenTarget_7b867462eca30b19
theorem M6.Transfer.small_polynomial_convolution : QuantumHarnessFrozenTarget := by
  change ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → _
  intro p q d hqdeg
  classical
  have hq : q = Polynomial.monomial 0 (q.coeff 0) +
      Polynomial.monomial 1 (q.coeff 1) + Polynomial.monomial 2 (q.coeff 2) := by
    ext n
    by_cases hn : n ≤ 2
    · interval_cases n <;> simp [Polynomial.coeff_monomial]
    · have hz : q.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simpa [Polynomial.coeff_monomial, show 0 ≠ n by omega,
        show 1 ≠ n by omega, show 2 ≠ n by omega] using hz
  have hm (n : ℕ) (r : ℤ) :
      (p * Polynomial.monomial n r).coeff d =
        if n ≤ d then p.coeff (d - n) * r else 0 := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc]
    simp [Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C]
  conv_lhs => rw [hq]
  simp [mul_add, Polynomial.coeff_add, hm, Fin.sum_univ_succ, add_assoc]
