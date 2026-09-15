import FrozenTarget_2c65fbdab56fb84a
theorem M6.ZeroSpan.boundary_trace_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N _
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  unfold M6.ActualTransfer.boundaryTrace
  simp only [hs]
  rw [M6.Transfer.scalar_trace_polynomial 0 N _ (by
    intro i m t
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2)]
  exact M6.ZeroSpan.zero_memory_trace N _ _ (M6.ZeroSpan.boundary_loops N)
