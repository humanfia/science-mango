import FrozenTarget_5076d6612193e649
theorem M6.ActualTransfer.actual_solve_storage : QuantumHarnessFrozenTarget := by
  intro N inst a b hspan
  have ha : a.natDegree ≤ N := by
    unfold M6.ActualTransfer.span at hspan
    omega
  have hb : b.natDegree ≤ N := by
    unfold M6.ActualTransfer.span at hspan
    omega
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hstorage := M6.EuclidStorage.preprocess_storage N a b
    (M6.Cyclic.modulus N) ha hb hM
  simpa only [M6.ActualTransfer.actualSolveStorage] using
    (M6.Transfer.solve_storage_bound (M6.ActualTransfer.span a b) N
      (M6.EuclidStorage.actualPreprocessStorage N) hspan hstorage.2.2)
