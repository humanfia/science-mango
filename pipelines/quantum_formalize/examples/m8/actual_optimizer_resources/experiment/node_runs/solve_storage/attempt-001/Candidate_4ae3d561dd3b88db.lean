import FrozenTarget_4ae3d561dd3b88db
theorem M8.OptimizerResources.solve_storage : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ 16384 * (N + 1)^3
  intro N inst a b h
  have hspan : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt h ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  calc
    M6.ActualTransfer.actualSolveStorage N a b ≤ 16384 * N^2 * 2^(M6.ActualTransfer.span a b) :=
      M6.ActualTransfer.actual_solve_storage N a b hspan
    _ ≤ 16384 * (N + 1)^3 := by
      simpa only [mul_assoc] using
        Nat.mul_le_mul_left 16384 (M8.Cutoff.indexed_storage_envelope N (M6.ActualTransfer.span a b) h)
