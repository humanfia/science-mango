import M6SolveResourcesReady

theorem M6.ActualTransfer.actual_distance_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*N^3*4^(M6.ActualTransfer.span a b) := by
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

theorem M6.ActualTransfer.actual_witness_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.span a b < N → M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*N^4*4^(M6.ActualTransfer.span a b) := by
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
#print axioms M6.ActualTransfer.actual_distance_work
#print axioms M6.ActualTransfer.actual_witness_work
