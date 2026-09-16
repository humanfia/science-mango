import FrozenTarget_2961ad594e804804
theorem M8.P4Gcd.cofactor_eval : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  unfold M8.P4Gcd.oddCofactor
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  change ((2 * m + 1 : ℕ) : ZMod 2) = 1
  norm_num [Nat.cast_add, Nat.cast_mul]
