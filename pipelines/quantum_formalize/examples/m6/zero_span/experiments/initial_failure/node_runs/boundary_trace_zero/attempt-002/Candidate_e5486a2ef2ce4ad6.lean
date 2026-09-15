import FrozenTarget_e5486a2ef2ce4ad6
theorem M6.ZeroSpan.boundary_trace_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N _
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  have hb : ∀ i m t,
      (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)) i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2*N) (M6.Pinned.free (2*N)) _ _ _ _).2
  have ht := M6.Transfer.scalar_trace_polynomial 0 N
    (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N))) hb
  have hz := M6.ZeroSpan.zero_memory_trace N
    (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)))
    ((1 : Polynomial ℤ) + Polynomial.X^2) (M6.ZeroSpan.boundary_loops N)
  simpa only [M6.ActualTransfer.boundaryTrace, hs] using ht.trans hz
