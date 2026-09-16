import FrozenTarget_c9e0427d51c79d29
theorem M8.Cutoff.bit_length_limit : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, M8.Cutoff.limit N = min (N - 1) (Nat.log2 (N + 1))
  intro N
  simp only [M8.Cutoff.limit, Nat.log2_eq_log_two]
