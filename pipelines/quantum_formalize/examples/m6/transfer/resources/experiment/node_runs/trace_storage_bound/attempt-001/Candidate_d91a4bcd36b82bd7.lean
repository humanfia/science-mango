import FrozenTarget_d91a4bcd36b82bd7
theorem M6.Transfer.trace_storage_bound : QuantumHarnessFrozenTarget := by
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
