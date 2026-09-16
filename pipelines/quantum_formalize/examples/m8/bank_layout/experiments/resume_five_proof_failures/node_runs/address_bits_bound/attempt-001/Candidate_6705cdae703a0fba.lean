import FrozenTarget_6705cdae703a0fba
theorem M8.BankLayout.address_bits_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (M8.BankLayout.payloadSlots N).size ≤ 32 * (N + 1)
  intro N hN
  apply Nat.size_le.mpr
  have hsmall : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ k := by positivity
      omega
  have hc : (20000 : ℕ) < 2 ^ 15 := by norm_num
  calc
    M8.BankLayout.payloadSlots N ≤ 20000 * (N + 1) ^ 3 := M8.BankLayout.payload_bound N
    _ ≤ 20000 * (2 ^ (N + 1)) ^ 3 := by
      gcongr
      exact hsmall (N + 1)
    _ < 2 ^ 15 * (2 ^ (N + 1)) ^ 3 :=
      Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = 2 ^ 15 * 2 ^ ((N + 1) * 3) := by rw [pow_mul]
    _ = 2 ^ (15 + (N + 1) * 3) := (pow_add (2 : ℕ) 15 ((N + 1) * 3)).symm
    _ ≤ 2 ^ (32 * (N + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
