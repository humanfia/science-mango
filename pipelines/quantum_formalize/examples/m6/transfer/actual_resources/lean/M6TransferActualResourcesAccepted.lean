import M6TransferActualResources

theorem M6.Transfer.actual_signed_capacity : ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1) := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1)
  intro R N
  change 2^R * 8^N < 2^(R + 3*N + 2 - 1)
  have h : R + 3*N + 2 - 1 = R + 3*N + 1 := by omega
  rw [h, show (8 : ℕ) = 2^3 by norm_num, ← pow_mul, ← pow_add, pow_succ]
  have hp : 0 < (2 : ℕ)^(R + 3*N) := by positivity
  omega

theorem M6.Transfer.actual_trace_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hspos : 0 < (2 : ℕ)^R := by positivity
  have hs : 1 ≤ (2 : ℕ)^R := by omega
  have hNN : N ≤ N^2 := by nlinarith
  have hscale : N ≤ N^2 * 2^R := by
    calc
      N ≤ N^2 := hNN
      _ = N^2 * 1 := by simp
      _ ≤ N^2 * 2^R := Nat.mul_le_mul_left _ hs
  have haddr : M6.Transfer.actualAddressBits R N ≤ 21*N := by
    unfold M6.Transfer.actualAddressBits
    omega
  have hcoeff : M6.Transfer.coefficientBits R N ≤ 6*N := by
    unfold M6.Transfer.coefficientBits
    omega
  have hlen : (M6.Transfer.scatterEventList R N).length = 6*(2*N+1)*2^R := by
    simp [M6.Transfer.scatterEventList, M6.Transfer.ScatterEvent,
      Fintype.card_prod, M6.Transfer.Bit, M6.Transfer.state_count,
      mul_assoc, mul_comm, mul_left_comm] <;> ring
  have hslots : 2*N+1 ≤ 3*N := by omega
  have hlenbound : (M6.Transfer.scatterEventList R N).length ≤ 18*N*2^R := by
    rw [hlen]
    nlinarith [Nat.mul_le_mul_right (6*2^R) hslots]
  have hrecord : 4*M6.Transfer.actualAddressBits R N+8 ≤ 92*N := by omega
  have hevents : (M6.Transfer.scatterEventList R N).length *
      (4*M6.Transfer.actualAddressBits R N+8) ≤ 1656*N^2*2^R := by
    calc
      _ ≤ (18*N*2^R)*(92*N) := Nat.mul_le_mul hlenbound hrecord
      _ = 1656*N^2*2^R := by ring
  have hscratch : 64*(M6.Transfer.coefficientBits R N +
      M6.Transfer.actualAddressBits R N) ≤ 1728*N^2*2^R := by
    nlinarith [Nat.mul_le_mul_left 1728 hscale]
  have hextra : 4*N ≤ 4*N^2*2^R := by
    nlinarith [Nat.mul_le_mul_left 4 hscale]
  have hbase := M6.Transfer.trace_storage_bound R N hRN
  unfold M6.Transfer.actualTraceStorage
  nlinarith

theorem M6.Transfer.actual_trace_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R
  intro R N hRN
  classical
  have hN : 1 ≤ N := by omega
  have hslots : 2 * N + 1 ≤ 3 * N := by omega
  have hcharge : M6.Transfer.actualEventBitCharge R N ≤ 616 * N := by
    unfold M6.Transfer.actualEventBitCharge M6.Transfer.coefficientBits M6.Transfer.actualAddressBits
    omega
  have hevents :
      Fintype.card (M6.Transfer.Memory R) * N *
        (M6.Transfer.scatterEventList R N).length =
        6 * N * (2 * N + 1) * 4^R := by
    simpa only [M6.Transfer.traceCoefficientOps, M6.Transfer.scatterEventList,
      Finset.length_toList, Finset.card_univ] using
      M6.Transfer.scatter_loop_count R N
  have hpow : (2^R)^2 = (4 : ℕ)^R := by
    calc
      (2^R)^2 = (2^2)^R := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm R 2]
      _ = 4^R := by norm_num
  have hcount :
      Fintype.card (M6.Transfer.Memory R) * N *
          (M6.Transfer.scatterEventList R N).length +
        (2^R)^2 * N * (2*N+1) ≤ 21 * N^2 * 4^R := by
    rw [hevents, hpow]
    calc
      6 * N * (2*N+1) * 4^R + 4^R * N * (2*N+1) =
          7 * N * (2*N+1) * 4^R := by ring
      _ ≤ 7 * N * (3*N) * 4^R :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (7 * N) hslots)
      _ = 21 * N^2 * 4^R := by ring
  unfold M6.Transfer.actualTraceWork
  calc
    _ ≤ (21 * N^2 * 4^R) * (616 * N) := Nat.mul_le_mul hcount hcharge
    _ = 12936 * (N^3 * 4^R) := by ring
    _ ≤ 16384 * (N^3 * 4^R) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 16384 * N^3 * 4^R := by ring

theorem M6.Transfer.actual_address_capacity : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N) := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N)
  intro R N hRN
  have hpow : ∀ n : ℕ, n ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ)^n := by positivity
      omega
  have hsq : N^2 ≤ ((2 : ℕ)^N)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hpow N) (hpow N)
  have heq : (2 : ℕ)^(R + 2*N + 12) = 4096 * (2^N)^2 * 2^R := by
    rw [show R + 2*N + 12 = R + N*2 + 12 by omega]
    simp only [pow_add, pow_mul]
    norm_num
    <;> ring
  calc
    M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R :=
      M6.Transfer.actual_trace_storage_bound R N hRN
    _ ≤ 4096 * (2^N)^2 * 2^R :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4096 hsq)
    _ = 2^(R + 2*N + 12) := heq.symm
    _ < 2^(M6.Transfer.actualAddressBits R N) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
      unfold M6.Transfer.actualAddressBits
      omega
#print axioms M6.Transfer.actual_signed_capacity
#print axioms M6.Transfer.actual_trace_storage_bound
#print axioms M6.Transfer.actual_address_capacity
#print axioms M6.Transfer.actual_trace_work_bound
