import FrozenTarget_fdd4e36c712dca9f
theorem M8.BankLayout.payload_bound : QuantumHarnessFrozenTarget := by
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
