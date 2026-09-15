import FrozenTarget_53d099bfde8e33d1
theorem M6.Transfer.division_difference_fits : QuantumHarnessFrozenTarget := by
  change ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1)
  intro R N z w j k hz hw
  have hzdiv : (z / (2 : ℤ)^j).natAbs ≤ z.natAbs := by
    have h := Int.abs_ediv_le_abs z ((2 : ℤ)^j)
    simp only [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hwdiv : (w / (2 : ℤ)^k).natAbs ≤ w.natAbs := by
    have h := Int.abs_ediv_le_abs w ((2 : ℤ)^k)
    simp only [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hsub : (z / (2 : ℤ)^j - w / (2 : ℤ)^k).natAbs ≤
      (z / (2 : ℤ)^j).natAbs + (w / (2 : ℤ)^k).natAbs := by
    have h := abs_sub_le (z / (2 : ℤ)^j) (w / (2 : ℤ)^k)
    simp only [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hcap := M6.Transfer.actual_signed_capacity R N
  have hsmall : (z / (2 : ℤ)^j - w / (2 : ℤ)^k).natAbs <
      2 ^ ((M6.Transfer.coefficientBits R N - 1) + 1) := by
    rw [pow_succ]
    omega
  apply lt_of_lt_of_le hsmall
  apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
  unfold M6.Transfer.queryCoefficientBits
  omega
