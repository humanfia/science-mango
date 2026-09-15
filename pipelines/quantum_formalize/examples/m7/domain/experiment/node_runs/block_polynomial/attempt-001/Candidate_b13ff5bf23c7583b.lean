import FrozenTarget_b13ff5bf23c7583b
theorem M7.Domain.block_polynomial : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.blockPolynomial N (M7.Supports.indicator A) = M7.Supports.polynomial A
  intro N inst A
  classical
  apply Polynomial.ext
  intro n
  unfold M6.Coordinates.blockPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin N)]
    · simpa [Polynomial.coeff_C_mul_X_pow, ZMod.val_natCast, Nat.mod_eq_of_lt hn] using
        (M7.Supports.indicator_coefficient N A (n : ZMod N)).symm
    · intro j hj hne
      have hval : j.val ≠ n := by
        intro h
        apply hne
        exact Fin.ext h
      simp [Polynomial.coeff_C_mul_X_pow, hval, Ne.symm hval]
    · simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (M7.Supports.degree_lt N A) (Nat.le_of_not_gt hn))]
    apply Finset.sum_eq_zero
    intro j hj
    have hval : j.val ≠ n := by
      intro h
      exact hn (h ▸ j.isLt)
    simp [Polynomial.coeff_C_mul_X_pow, hval, Ne.symm hval]
