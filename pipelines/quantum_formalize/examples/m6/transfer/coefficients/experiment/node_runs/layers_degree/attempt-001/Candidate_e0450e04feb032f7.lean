import FrozenTarget_e0450e04feb032f7
theorem M6.Transfer.layers_degree : QuantumHarnessFrozenTarget := by
  classical
  intro R W start finish n hW
  induction n generalizing finish with
  | zero =>
      simp [M6.Transfer.layers]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate]
      apply Polynomial.natDegree_sum_le_of_forall
      intro m hm
      apply Polynomial.natDegree_sum_le_of_forall
      intro t ht
      split_ifs
      · calc
          (M6.Transfer.layers W start n m * W n m t).natDegree ≤
              (M6.Transfer.layers W start n m).natDegree + (W n m t).natDegree :=
            Polynomial.natDegree_mul_le _ _
          _ ≤ 2 * n + 2 := Nat.add_le_add (ih m) (hW n m t)
          _ = 2 * (n + 1) := by omega
      · simp
