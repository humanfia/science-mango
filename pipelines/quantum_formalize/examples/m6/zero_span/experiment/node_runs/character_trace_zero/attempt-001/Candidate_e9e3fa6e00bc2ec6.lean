import FrozenTarget_e9e3fa6e00bc2ec6
theorem M6.ZeroSpan.character_trace_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.characterTrace N 1 1 (M6.Pinned.free (2*N)) = Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N hN
  classical
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  have hb : ∀ i m t,
      (M6.ActualTransfer.characterWeight 0 N 1 1 (M6.Pinned.free (2*N)) i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
  unfold M6.ActualTransfer.characterTrace
  rw [hs]
  rw [M6.Transfer.scalar_trace_polynomial 0 N _ hb]
  rw [M6.ZeroSpan.zero_memory_trace N _
    (Polynomial.C 2 * ((1 : Polynomial ℤ) + Polynomial.X^2))
    (M6.ZeroSpan.character_loops N)]
  rw [mul_pow, ← Polynomial.C_pow]
