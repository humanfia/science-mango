import M6QueryResources

theorem M6.Transfer.paired_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192*N^2*2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := by omega
  have hp : 1 ≤ 2^R := Nat.one_le_pow R 2 (by omega)
  have hNN : N ≤ N^2 := by nlinarith
  have hRP : R * 2^R ≤ N * 2^R := Nat.mul_le_mul_right _ hR
  have hNP : N * 2^R ≤ N^2 * 2^R := Nat.mul_le_mul_right _ hNN
  have hP : 2^R ≤ N * 2^R := by nlinarith
  have hN2P : N^2 ≤ N^2 * 2^R := by nlinarith
  have hRNP : R * N * 2^R ≤ N^2 * 2^R := by
    calc
      R * N * 2^R ≤ N * N * 2^R := by gcongr
      _ = N^2 * 2^R := by ring
  have hs := M6.Transfer.actual_trace_storage_bound R N hRN
  simp only [M6.Transfer.pairedQueryStorage, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.PostEvent, Fintype.card_prod, Fintype.card_fin]
  first
  | nlinarith
  | simp only [M6.Transfer.actualTraceStorage, M6.Transfer.traceStorageModel,
      M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
      M6.Transfer.addressBits, M6.Transfer.CoefficientAddress,
      Fintype.card_prod, Fintype.card_fin, M6.Transfer.state_count]
    nlinarith

theorem M6.Transfer.paired_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000*N^3*4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000 * N^3 * 4^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hRN1 : R * N ≤ N^2 := by nlinarith [Nat.mul_le_mul_right N hR]
  have hRN2 : R * N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_right (N^2) hR]
  have hscale : N^3 ≤ N^3 * 4^R := by simpa using Nat.mul_le_mul_left (N^3) h4
  have hw := M6.Transfer.actual_trace_work_bound R N hRN
  have hp : M6.Transfer.postWork R N ≤ 7232 * N^3 * 4^R := by
    simp [M6.Transfer.postWork, M6.Transfer.PostEvent,
      M6.Transfer.queryCoefficientBits, M6.Transfer.coefficientBits,
      M6.Transfer.actualAddressBits, M6.Transfer.addressBits]
    <;> nlinarith
  unfold M6.Transfer.pairedQueryWork
  nlinarith

theorem M6.Transfer.post_event_count : ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4*(2*N+1) := by
  change ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4 * (2 * N + 1)
  intro N
  simp [M6.Transfer.PostEvent, M6.Transfer.Bit, Fintype.card_prod] <;> ring

theorem M6.Transfer.distance_work_bound : ∀ R N e : ℕ, R < N → e ≤ 180*(N+1)^3 → M6.Transfer.distanceWork R N e ≤ 50000*N^3*4^R := by
  change ∀ R N e : ℕ, R < N → e ≤ 180 * (N + 1)^3 → M6.Transfer.distanceWork R N e ≤ 50000 * N^3 * 4^R
  intro R N e hRN he
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hRN1 : R * N ≤ N^2 := by nlinarith [Nat.mul_le_mul_right N hR]
  have hRN2 : R * N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_right (N^2) hR]
  have hcube : (N + 1)^3 ≤ 8 * N^3 := by nlinarith
  have he' : e ≤ 1440 * N^3 := by omega
  have hscale : N^3 ≤ N^3 * 4^R := by simpa using Nat.mul_le_mul_left (N^3) h4
  have hp := M6.Transfer.paired_work_bound R N hRN
  simp [M6.Transfer.distanceWork, M6.Transfer.pinMaintenanceWork,
    M6.Transfer.PostEvent, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.addressBits]
  <;> nlinarith

theorem M6.Transfer.solve_storage_bound : ∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots ≤ 16384*N^2*2^R := by
  change ∀ R N slots : ℕ, R < N → slots ≤ 512 * (N + 1)^2 → M6.Transfer.solveStorage R N slots ≤ 16384 * N^2 * 2^R
  intro R N slots hRN hslots
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := by omega
  have hp : 1 ≤ 2^R := Nat.one_le_pow R 2 (by omega)
  have hNN : N ≤ N^2 := by nlinarith
  have hN2P : N^2 ≤ N^2 * 2^R := by nlinarith
  have hNP : N * 2^R ≤ N^2 * 2^R := Nat.mul_le_mul_right _ hNN
  have hRP : R * 2^R ≤ N * 2^R := Nat.mul_le_mul_right _ hR
  have hP : 2^R ≤ N * 2^R := by nlinarith
  have hslots' : slots ≤ 2048 * (N^2 * 2^R) := by nlinarith
  have hs := M6.Transfer.paired_storage_bound R N hRN
  simp only [M6.Transfer.solveStorage, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.PostEvent, Fintype.card_prod, Fintype.card_fin]
  nlinarith

theorem M6.Transfer.witness_work_bound : ∀ R N e k : ℕ, R < N → e ≤ 180*(N+1)^3 → k ≤ 2*N → M6.Transfer.witnessWork R N e k ≤ 200000*N^4*4^R := by
  change ∀ R N e k : ℕ, R < N → e ≤ 180 * (N + 1)^3 → k ≤ 2 * N → M6.Transfer.witnessWork R N e k ≤ 200000 * N^4 * 4^R
  intro R N e k hRN he hk
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hN4 : N^3 ≤ N^4 := by nlinarith [Nat.mul_le_mul_left N hN3]
  have he' : e ≤ 1440 * N^3 := by
    nlinarith [show (N + 1)^3 ≤ (2 * N)^3 from Nat.pow_le_pow_left (by omega) 3]
  have heN : e * N ≤ 1440 * N^4 := by
    nlinarith [Nat.mul_le_mul_right N he']
  have heR : e * R ≤ 1440 * N^4 := by
    nlinarith [Nat.mul_le_mul_left e hR]
  have hkN : k * N ≤ 2 * N^2 := by
    nlinarith [Nat.mul_le_mul_right N hk]
  have hkN2 : k * N^2 ≤ 2 * N^3 := by
    nlinarith [Nat.mul_le_mul_right (N^2) hk]
  have hkR : k * R ≤ 2 * N^2 := by
    nlinarith [Nat.mul_le_mul_left k hR]
  have hkRN : k * R * N ≤ 2 * N^3 := by
    nlinarith [Nat.mul_le_mul_right N hkR]
  have hRN' : R * N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul_right N hR]
  have hs3 : N^3 ≤ N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_left (N^4) h4]
  have hs4 : N^4 ≤ N^4 * 4^R := by
    simpa using Nat.mul_le_mul_left (N^4) h4
  have hp := M6.Transfer.paired_work_bound R N hRN
  have hpN : N * M6.Transfer.pairedQueryWork R N ≤ 40000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_left N hp]
  have hpk : k * M6.Transfer.pairedQueryWork R N ≤ 80000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_right (M6.Transfer.pairedQueryWork R N) hk]
  have hp' : M6.Transfer.pairedQueryWork R N ≤ 40000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_right (M6.Transfer.pairedQueryWork R N) hN]
  simp [M6.Transfer.witnessWork, M6.Transfer.distanceWork,
    M6.Transfer.pinMaintenanceWork, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.addressBits]
  <;> nlinarith
#print axioms M6.Transfer.paired_storage_bound
#print axioms M6.Transfer.paired_work_bound
#print axioms M6.Transfer.distance_work_bound
#print axioms M6.Transfer.post_event_count
#print axioms M6.Transfer.solve_storage_bound
#print axioms M6.Transfer.witness_work_bound
