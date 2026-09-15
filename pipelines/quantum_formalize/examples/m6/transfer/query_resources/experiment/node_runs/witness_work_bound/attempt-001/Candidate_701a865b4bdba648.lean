import FrozenTarget_701a865b4bdba648
theorem M6.Transfer.witness_work_bound : QuantumHarnessFrozenTarget := by
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
