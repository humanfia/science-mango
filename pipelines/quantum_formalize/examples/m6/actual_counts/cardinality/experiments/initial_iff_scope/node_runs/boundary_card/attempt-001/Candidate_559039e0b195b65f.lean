import FrozenTarget_559039e0b195b65f
theorem M6.ActualCounts.boundary_card : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  have h := M6.ActualCounts.input_normalization N a b ha hb
  rw [M6.Spaces.dual_boundary_card] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : M6.ActualCounts.f N a b + (N - M6.ActualCounts.f N a b) = N := by
    omega
  have hpow : (2 : ℕ)^N = 2^(M6.ActualCounts.f N a b) * 2^(N - M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow
