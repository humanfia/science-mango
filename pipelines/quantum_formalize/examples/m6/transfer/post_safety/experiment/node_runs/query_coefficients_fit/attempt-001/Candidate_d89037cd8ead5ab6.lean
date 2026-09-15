import FrozenTarget_d89037cd8ead5ab6
theorem M6.ActualTransfer.query_coefficients_fit : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1)
  intro N inst a b P d
  have hb : ((M6.ActualTransfer.boundaryTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.boundaryTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).1
  have hc : ((M6.ActualTransfer.characterTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.characterTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  unfold M6.ActualTransfer.Q
  simp only [Polynomial.coeff_sub, M6.Normalize.divide_coeff]
  apply M6.Transfer.division_difference_fits <;> assumption
