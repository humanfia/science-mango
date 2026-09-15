import FrozenTarget_a94b81d227de190a
theorem M6.ActualTransfer.boundary_trace_inputs : QuantumHarnessFrozenTarget := by
  intro N inst a b hspan P
  classical
  unfold M6.ActualTransfer.boundaryTrace
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2 * N) P _ _ _ _).2
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.boundary_input_product
    (M6.ActualTransfer.span a b) N a b
    (by simpa only [M6.ActualTransfer.span] using (le_max_left a.natDegree b.natDegree))
    (by simpa only [M6.ActualTransfer.span] using (le_max_right a.natDegree b.natDegree))
    hspan P h
