import FrozenTarget_e4f2cb9dfe1e1ae3
theorem M6.ActualCounts.cycle_card : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  have h := M6.Character.dual_cardinality (2 * N)
    (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
  change (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))).card *
    (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(2 * N) at h
  rw [M6.Spaces.dual_boundary_card, M6.ActualCounts.boundary_card N a b ha hb] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : (N - M6.ActualCounts.f N a b) + (N + M6.ActualCounts.f N a b) = 2 * N := by
    omega
  have hpow : (2 : ℕ)^(2 * N) = 2^(N - M6.ActualCounts.f N a b) * 2^(N + M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(N - M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow
