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

theorem M8.BankLayout.workspace_monotone : ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots := by
  intro R S N slots hRS
  have hpow : (2 : ℕ)^R ≤ 2^S := pow_le_pow_right₀ (by decide) hRS
  unfold M6.Transfer.solveStorage M6.Transfer.pairedQueryStorage M6.Transfer.actualTraceStorage M6.Transfer.traceStorageModel
  simp only [M6.Transfer.scatterEventList, Finset.length_toList, Finset.card_univ,
    M6.Transfer.ScatterEvent, Fintype.card_prod, M6.Transfer.state_count,
    M6.Transfer.Bit, ZMod.card, Fintype.card_fin,
    M6.Transfer.queryCoefficientBits, M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits]
  gcongr <;> first | exact hRS | exact hpow | omega

theorem M8.BankLayout.actual_workspace_fits : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ M8.BankLayout.bankSlots N := by
  intro N inst a b h
  change M6.Transfer.solveStorage (M6.ActualTransfer.span a b) N (M6.EuclidStorage.actualPreprocessStorage N) ≤ M6.Transfer.solveStorage (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N)
  exact M8.BankLayout.workspace_monotone (M6.ActualTransfer.span a b) (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N) h

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
#print axioms M8.BankLayout.workspace_monotone
#print axioms M8.BankLayout.actual_workspace_fits
