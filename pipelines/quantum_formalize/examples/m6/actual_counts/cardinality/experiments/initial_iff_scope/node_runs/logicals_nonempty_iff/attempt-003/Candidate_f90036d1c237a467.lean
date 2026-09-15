import FrozenTarget_f90036d1c237a467
theorem M6.ActualCounts.logicals_nonempty_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).Nonempty ↔ 0 < M6.ActualCounts.f N a b)
  intro N inst a b
  intro ha hb
  rw [← Finset.card_pos]
  have hc := M6.ActualCounts.logical_card N a b ha hb
  constructor
  · intro hpos
    by_contra hn
    have hz : M6.ActualCounts.f N a b = 0 := by omega
    simp only [hz, Nat.add_zero, Nat.sub_zero, sub_self] at hc
    have hposZ : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by exact_mod_cast hpos
    omega
  · intro hf
    have he : N - M6.ActualCounts.f N a b < N + M6.ActualCounts.f N a b := by omega
    have hp : (2 : ℤ) ^ (N - M6.ActualCounts.f N a b) < (2 : ℤ) ^ (N + M6.ActualCounts.f N a b) := by
      exact pow_lt_pow_right₀ (by norm_num) he
    have hposZ : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by omega
    exact_mod_cast hposZ
