import FrozenTarget_da4d1d4a8b61b733
theorem M6.ActualCounts.logicals_nonempty_iff : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  classical
  rw [← Finset.card_pos]
  have hc := M6.ActualCounts.logical_card N a b ha hb
  constructor
  · intro hpos
    by_contra h
    have hf0 : M6.ActualCounts.f N a b = 0 := by omega
    simp only [hf0, Nat.add_zero, Nat.sub_zero, sub_self] at hc
    have hpos' : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      exact_mod_cast hpos
    omega
  · intro hf
    have hexp : N - M6.ActualCounts.f N a b < N + M6.ActualCounts.f N a b := by omega
    have hp : (2 : ℤ) ^ (N - M6.ActualCounts.f N a b) < (2 : ℤ) ^ (N + M6.ActualCounts.f N a b) :=
      pow_lt_pow_right₀ (by norm_num) hexp
    have hpos : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      rw [hc]
      exact sub_pos.mpr hp
    exact_mod_cast hpos
