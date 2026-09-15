import FrozenTarget_c395dd2312011690
theorem M6.ActualTransfer.character_trace_inputs : QuantumHarnessFrozenTarget := by
  intro N inst a b hspan P
  classical
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds (2*N) P _ _ _ _).2
  unfold M6.ActualTransfer.characterTrace
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.character_input_product
    (M6.ActualTransfer.span a b) N a b
    (by unfold M6.ActualTransfer.span; exact le_max_left _ _)
    (by unfold M6.ActualTransfer.span; exact le_max_right _ _)
    hspan P h
