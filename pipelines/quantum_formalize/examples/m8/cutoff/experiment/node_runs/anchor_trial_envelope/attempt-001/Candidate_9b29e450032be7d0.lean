import FrozenTarget_9b29e450032be7d0
theorem M8.Cutoff.anchor_trial_envelope : QuantumHarnessFrozenTarget := by
  change ∀ (N a b : ℕ), a ≤ N → b ≤ N → 2 * N * a * b ≤ 2 * N ^ 3
  intro N a b ha hb
  calc
    2 * N * a * b ≤ 2 * N * N * N :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 * N) ha) hb
    _ = 2 * N ^ 3 := by ring
