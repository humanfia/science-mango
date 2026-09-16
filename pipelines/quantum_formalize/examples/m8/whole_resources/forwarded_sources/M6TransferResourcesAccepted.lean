import M6TransferResources

theorem M6.Transfer.address_width : ∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2^(M6.Transfer.addressBits R N) := by
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

theorem M6.Transfer.coefficient_width : ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N) := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(R + 3*N + 2)
  intro R N
  have h : 0 < (2 : ℕ)^R * 8^N := by positivity
  norm_num [pow_add, pow_mul] <;> nlinarith

theorem M6.Transfer.state_count : ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R := by
  change ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2 ^ R
  intro R
  simp [M6.Transfer.Memory, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]

theorem M6.Transfer.trace_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hp : 1 ≤ (2 : ℕ)^R := by
    have : 0 < (2 : ℕ)^R := by positivity
    omega
  have hc : M6.Transfer.coefficientBits R N ≤ 6*N := by
    unfold M6.Transfer.coefficientBits
    omega
  have hs : 2*N+1 ≤ 3*N := by omega
  have hr : R+2 ≤ 3*N := by omega
  have h1 : 2 * 2^R * (2*N+1) * M6.Transfer.coefficientBits R N ≤ 36 * N^2 * 2^R := by
    calc
      2 * 2^R * (2*N+1) * M6.Transfer.coefficientBits R N
          ≤ 2 * 2^R * (3*N) * (6*N) := by gcongr
      _ = 36 * N^2 * 2^R := by ring
  have h2 : (2*N+1) * M6.Transfer.coefficientBits R N ≤ 18 * N^2 := by
    calc
      (2*N+1) * M6.Transfer.coefficientBits R N ≤ (3*N) * (6*N) := by gcongr
      _ = 18 * N^2 := by ring
  have h3 : 2 * 2^R * (R+2) ≤ 6 * N * 2^R := by
    calc
      2 * 2^R * (R+2) ≤ 2 * 2^R * (3*N) := by gcongr
      _ = 6 * N * 2^R := by ring
  have hn2 : N ≤ N^2 := by nlinarith
  have hb : N^2 ≤ N^2 * 2^R := by
    simpa using Nat.mul_le_mul_left (N^2) hp
  have hnp : N * 2^R ≤ N^2 * 2^R :=
    Nat.mul_le_mul_right (2^R) hn2
  have hnT : N ≤ N^2 * 2^R := le_trans hn2 hb
  have hT : 1 ≤ N^2 * 2^R := le_trans hN hnT
  unfold M6.Transfer.traceStorageModel
  nlinarith

theorem M6.Transfer.scatter_loop_count : ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2*N+1) * 4^R := by
  change ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2 * N + 1) * 4 ^ R
  intro R N
  simp only [M6.Transfer.traceCoefficientOps, M6.Transfer.ScatterEvent,
    Fintype.card_prod, M6.Transfer.state_count, Fintype.card_fin,
    M6.Transfer.Bit, ZMod.card]
  have hpow : (4 : ℕ) ^ R = 2 ^ R * 2 ^ R := by
    simpa using (mul_pow (2 : ℕ) 2 R)
  rw [hpow]
  ring

theorem M6.Transfer.trace_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hslots : 2 * N + 1 ≤ 3 * N := by omega
  have hcharge : M6.Transfer.eventBitCharge R N ≤ 60 * N := by
    unfold M6.Transfer.eventBitCharge M6.Transfer.coefficientBits M6.Transfer.addressBits
    omega
  have hpow : ((2 : ℕ)^R)^2 = 4^R := by
    calc
      (2^R)^2 = 2^R * 2^R := by ring
      _ = (2 * 2)^R := (mul_pow (2 : ℕ) 2 R).symm
      _ = 4^R := by norm_num
  have hcount : M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1) ≤ 21 * N^2 * 4^R := by
    rw [M6.Transfer.scatter_loop_count, hpow]
    calc
      6 * N * (2*N+1) * 4^R + 4^R * N * (2*N+1)
          = (7 * N * 4^R) * (2*N+1) := by ring
      _ ≤ (7 * N * 4^R) * (3*N) := Nat.mul_le_mul_left _ hslots
      _ = 21 * N^2 * 4^R := by ring
  unfold M6.Transfer.traceWorkModel
  calc
    (M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1)) * M6.Transfer.eventBitCharge R N
        ≤ (21 * N^2 * 4^R) * (60*N) := Nat.mul_le_mul hcount hcharge
    _ = 1260 * (N^3 * 4^R) := by ring
    _ ≤ 4096 * (N^3 * 4^R) := Nat.mul_le_mul_right _ (by decide : (1260 : ℕ) ≤ 4096)
    _ = 4096 * N^3 * 4^R := by ring
#print axioms M6.Transfer.address_width
#print axioms M6.Transfer.coefficient_width
#print axioms M6.Transfer.state_count
#print axioms M6.Transfer.scatter_loop_count
#print axioms M6.Transfer.trace_storage_bound
#print axioms M6.Transfer.trace_work_bound
