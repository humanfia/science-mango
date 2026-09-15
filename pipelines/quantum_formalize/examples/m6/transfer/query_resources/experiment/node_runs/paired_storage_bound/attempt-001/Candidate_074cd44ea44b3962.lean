import FrozenTarget_074cd44ea44b3962
theorem M6.Transfer.paired_storage_bound : QuantumHarnessFrozenTarget := by
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
