import FrozenTarget_66abc386c0bbac92
theorem M6.Transfer.distance_work_bound : QuantumHarnessFrozenTarget := by
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
