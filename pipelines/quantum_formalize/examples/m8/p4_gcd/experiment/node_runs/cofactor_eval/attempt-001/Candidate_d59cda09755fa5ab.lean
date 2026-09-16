import FrozenTarget_d59cda09755fa5ab
theorem M8.P4Gcd.cofactor_eval : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  norm_num [M8.P4Gcd.oddCofactor, Polynomial.eval_finset_sum, Nat.cast_add, Nat.cast_mul]
