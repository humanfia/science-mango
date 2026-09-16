import FrozenTarget_da77d9e3dffa9e1e
theorem M8.P4Gcd.cofactor_eval : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  simp [M8.P4Gcd.oddCofactor, Polynomial.eval_finset_sum, Nat.cast_add, Nat.cast_mul] <;> norm_num
