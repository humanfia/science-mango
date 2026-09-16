import FrozenTarget_dca1ecd99ba18a3e
theorem M8.Exclusion.antipodal_complete : QuantumHarnessFrozenTarget := by
  intro N inst v hv hN
  have h8 : 8 ≤ N := by
    rw [hN]
    calc
      8 = (2 : ℕ)^3 := by norm_num
      _ ≤ 2^v := by gcongr <;> omega
  have hmul : N = 2 * 2^(v-1) := by
    calc
      N = 2^v := hN
      _ = 2^((v-1)+1) := by congr 1; omega
      _ = 2 * 2^(v-1) := by simp [pow_succ, Nat.mul_comm]
  have heven : Even N := ⟨2^(v-1), by omega⟩
  have hhalf : N/2 = 2^(v-1) := by omega
  have hp : M8.AntipodalFamily.polynomial N =
      (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(N/2+1) := by
    calc
      M8.AntipodalFamily.polynomial N =
          (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1) := by
        rw [hN]
        exact M8.AntipodalFamily.polynomial_power v hv
      _ = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(N/2+1) := by rw [hhalf]
  refine ⟨M8.AntipodalFamily.valid N h8 heven, ?_, ?_, M8.Exclusion.antipodal_distance N v hv hN⟩
  · exact (M8.AntipodalFamily.signature N v hv hN).trans hp
  · rw [← hp]
    exact M8.Exclusion.antipodal_rejected N v hv hN
