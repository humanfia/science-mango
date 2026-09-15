import FrozenTarget_8bd3b8dc0176b1c8
theorem M6.ActualTransfer.actual_distance_work : QuantumHarnessFrozenTarget := by
  intro N inst a b hspan
  have ha : a.natDegree ≤ N := by
    have h := (max_le_iff.mp (Nat.le_of_lt hspan : M6.ActualTransfer.span a b ≤ N)).1
    exact h
  have hb : b.natDegree ≤ N := by
    have h := (max_le_iff.mp (Nat.le_of_lt hspan : M6.ActualTransfer.span a b ≤ N)).2
    exact h
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    change (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).natDegree ≤ N
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hcost := (M6.Euclid.preprocess_correct_cost N a b (M6.Cyclic.modulus N) ha hb hM).2
  unfold M6.ActualTransfer.actualDistanceWork
  exact M6.Transfer.distance_work_bound (M6.ActualTransfer.span a b) N _ hspan hcost
