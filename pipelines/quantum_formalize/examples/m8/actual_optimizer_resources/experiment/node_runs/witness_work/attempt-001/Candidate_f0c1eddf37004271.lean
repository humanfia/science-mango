import FrozenTarget_f0c1eddf37004271
theorem M8.OptimizerResources.witness_work : QuantumHarnessFrozenTarget := by
  intro N inst a b d v k hcut hsolve
  have hspan : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt hcut ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  refine le_trans (M6.ActualTransfer.actual_witness_work N a b d v k hspan hsolve) ?_
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 200000
      ((M8.Cutoff.indexed_work_envelopes N (M6.ActualTransfer.span a b) hcut).2)
