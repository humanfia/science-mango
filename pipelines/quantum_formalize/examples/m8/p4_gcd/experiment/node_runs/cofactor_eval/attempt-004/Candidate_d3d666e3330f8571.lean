import FrozenTarget_d3d666e3330f8571
theorem M8.P4Gcd.cofactor_eval : QuantumHarnessFrozenTarget := by
  intro m
  simp [M8.P4Gcd.oddCofactor, Polynomial.eval_finsetSum, Nat.cast_add, Nat.cast_mul] <;> norm_num
