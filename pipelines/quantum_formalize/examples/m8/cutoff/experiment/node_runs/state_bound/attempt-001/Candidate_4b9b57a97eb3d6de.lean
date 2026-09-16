import FrozenTarget_4b9b57a97eb3d6de
theorem M8.Cutoff.state_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2 ^ R ≤ N + 1
  intro N R hR
  have hlog : R ≤ Nat.log 2 (N + 1) :=
    le_trans hR (M8.Cutoff.limit_bounds N).2.1
  calc
    2 ^ R ≤ 2 ^ Nat.log 2 (N + 1) := by
      gcongr
    _ ≤ N + 1 := by
      apply Nat.pow_log_le_self
      omega
