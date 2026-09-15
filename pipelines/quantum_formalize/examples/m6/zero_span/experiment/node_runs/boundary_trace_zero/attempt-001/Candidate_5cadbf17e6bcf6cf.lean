import FrozenTarget_5cadbf17e6bcf6cf
theorem M6.ZeroSpan.boundary_trace_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N _
  classical
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  unfold M6.ActualTransfer.boundaryTrace
  rw [hs]
  trans M6.Transfer.arrayTrace (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N))) N
  · apply M6.Transfer.scalar_trace_polynomial
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2*N) (M6.Pinned.free (2*N)) _ _ _ _).2
  · exact M6.ZeroSpan.zero_memory_trace N _ _ (M6.ZeroSpan.boundary_loops N)
