import FrozenTarget_69c9fa8796ffede0
theorem M6.Transfer.layers_degree : QuantumHarnessFrozenTarget := by
  classical
  intro R W start finish n hW
  induction n generalizing finish with
  | zero =>
      by_cases h : finish = start <;>
        simp [M6.Transfer.layers, h]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro m hm
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t ht
      split_ifs with h
      · have hmul := Polynomial.natDegree_mul_le (p := M6.Transfer.layers W start n m) (q := W n m t)
        exact (hmul.trans (Nat.add_le_add (ih m) (hW n m t))).trans_eq (by simp [Nat.mul_succ])
      · simp
