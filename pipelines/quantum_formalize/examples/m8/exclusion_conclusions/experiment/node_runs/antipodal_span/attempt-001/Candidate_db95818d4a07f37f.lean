import FrozenTarget_db95818d4a07f37f
theorem M8.Exclusion.antipodal_span : QuantumHarnessFrozenTarget := by
  intro N inst v hv hN
  have hc := M8.AntipodalFamily.cutoff_half v hv
  have hmul : N = 2 * 2^(v-1) := by
    calc
      N = 2^v := hN
      _ = 2^((v-1)+1) := by congr 1; omega
      _ = 2 * 2^(v-1) := by simp [pow_succ, Nat.mul_comm]
  have hhalf : N/2 = 2^(v-1) := by omega
  have h8 : 8 ≤ N := by omega
  have heven : Even N := ⟨2^(v-1), by omega⟩
  have hd := M8.AntipodalFamily.support_data N h8 heven
  have ha : M8.ExclusionGeometry.Antipodal (N/2) (M8.AntipodalFamily.support N) := by
    refine ⟨0, hd.2.1, ?_⟩
    simpa only [zero_add] using hd.2.2.2
  apply M8.ExclusionGeometry.antipodal_exclusion N (N/2) (M8.Cutoff.limit N) (M8.AntipodalFamily.recipe N)
  · omega
  · exact Or.inl ha
  · rw [hN, hc.1]
    rw [hN] at hhalf
    omega
