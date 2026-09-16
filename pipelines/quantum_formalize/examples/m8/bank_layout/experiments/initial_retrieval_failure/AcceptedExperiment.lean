import M8BankLayout

theorem M8.BankLayout.payload_bound : ∀ (N : ℕ) [NeZero N], M8.BankLayout.payloadSlots N ≤ 20000*(N+1)^3 := by
  change ∀ (N : ℕ) [NeZero N], M8.BankLayout.payloadSlots N ≤ 20000 * (N + 1)^3
  intro N hN
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcut : M8.Cutoff.limit N < N := (M8.Cutoff.limit_bounds N).2.2 hpos
  have hpre := (M6.EuclidStorage.layout_bound N).2.2
  have hb := M6.Transfer.solve_storage_bound (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N) hcut hpre
  have he := M8.Cutoff.indexed_storage_envelope N (M8.Cutoff.limit N) (le_refl _)
  have hbank : M8.BankLayout.bankSlots N ≤ 16384 * (N + 1)^3 := by
    unfold M8.BankLayout.bankSlots
    calc
      _ ≤ 16384 * N^2 * 2^(M8.Cutoff.limit N) := hb
      _ ≤ 16384 * (N + 1)^3 := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 16384 he
  norm_num [M8.BankLayout.payloadSlots, M8.BankLayout.bufferWidths, M8.BankLayout.registers, M8.BankLayout.registerBits]
  nlinarith [hbank, Nat.zero_le (N^3), Nat.zero_le (N^2)]

theorem M8.BankLayout.address_bits_bound : ∀ (N : ℕ) [NeZero N], (M8.BankLayout.payloadSlots N).size ≤ 32*(N+1) := by
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
#print axioms M8.BankLayout.payload_bound
#print axioms M8.BankLayout.address_bits_bound
