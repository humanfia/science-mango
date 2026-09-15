import FrozenTarget_820932ece66821ae
theorem M6.Transfer.address_width : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2 ^ (M6.Transfer.addressBits R N)
  intro R N hN
  have hbound : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hsquare : (N + 1) ^ 2 ≤ (2 ^ N) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hbound N) (hbound N)
  change 16 * 2 ^ R * (N + 1) ^ 2 ≤ 2 ^ (R + 2 * N + 4)
  calc
    16 * 2 ^ R * (N + 1) ^ 2 ≤ 16 * 2 ^ R * (2 ^ N) ^ 2 :=
      Nat.mul_le_mul_left _ hsquare
    _ = 2 ^ (R + 2 * N + 4) := by
      rw [pow_add, pow_add, Nat.mul_comm 2 N, pow_mul]
      ring
