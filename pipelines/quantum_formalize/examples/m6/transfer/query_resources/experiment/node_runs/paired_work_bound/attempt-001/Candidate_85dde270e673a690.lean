import FrozenTarget_85dde270e673a690
theorem M6.Transfer.paired_work_bound : QuantumHarnessFrozenTarget := by
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
