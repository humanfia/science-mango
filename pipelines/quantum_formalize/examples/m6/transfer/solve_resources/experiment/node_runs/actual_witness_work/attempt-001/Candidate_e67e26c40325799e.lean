import FrozenTarget_e67e26c40325799e
theorem M6.ActualTransfer.actual_witness_work : QuantumHarnessFrozenTarget := by
  intro N inst a b d v k hspan hsolve
  have ha : a.natDegree ≤ N := by
    have h : max a.natDegree b.natDegree < N := hspan
    exact (le_max_left _ _).trans (Nat.le_of_lt h)
  have hb : b.natDegree ≤ N := by
    have h : max a.natDegree b.natDegree < N := hspan
    exact (le_max_right _ _).trans (Nat.le_of_lt h)
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    change (Polynomial.X ^ N + 1 : Polynomial (ZMod 2)).natDegree ≤ N
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have he := (M6.Euclid.preprocess_correct_cost N a b (M6.Cyclic.modulus N) ha hb hM).2
  have hk := M6.ActualTransfer.actual_solve_queries N a b d v k hsolve
  unfold M6.ActualTransfer.actualWitnessWork
  exact M6.Transfer.witness_work_bound (M6.ActualTransfer.span a b) N _ k hspan he hk
