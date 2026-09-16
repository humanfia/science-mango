import FrozenTarget_a2f32f4354c65e37
theorem M8.Exclusion.antipodal_rejected : QuantumHarnessFrozenTarget := by
  intro N inst v hv hN
  have hc := M8.AntipodalFamily.cutoff_half v hv
  have hmul : N = 2 * 2^(v-1) := by
    calc
      N = 2^v := hN
      _ = 2^((v-1)+1) := by congr 1; omega
      _ = 2 * 2^(v-1) := by simp [pow_succ, Nat.mul_comm]
  have h8 : 8 ≤ N := by omega
  have heven : Even N := ⟨2^(v-1), by omega⟩
  have hsig : M8.PhysicalBridge.signature (M8.AntipodalFamily.recipe N) = M8.AntipodalFamily.polynomial N := by
    exact M8.AntipodalFamily.signature N v hv hN
  rw [← hsig]
  apply M8.Exclusion.span_rejected N 4 (M8.AntipodalFamily.recipe N)
  · norm_num
  · exact M8.AntipodalFamily.valid N h8 heven
  · rw [hsig]
    exact (M8.AntipodalFamily.nontrivial N h8 heven).2.1
  · exact M8.Exclusion.antipodal_span N v hv hN
