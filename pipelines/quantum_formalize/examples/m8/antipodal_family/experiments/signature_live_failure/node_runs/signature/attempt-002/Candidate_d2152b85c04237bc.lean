import FrozenTarget_d2152b85c04237bc
theorem M8.AntipodalFamily.signature : QuantumHarnessFrozenTarget := by
    classical
    intro N inst v hv hN
    have h8 : 8 ≤ N := by
      rw [hN]
      calc
        8 = (2 : ℕ) ^ 3 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv
    have heven : Even N := by
      refine ⟨2 ^ (v - 1), ?_⟩
      rw [hN]
      have hpow : (2 : ℕ) ^ v = 2 ^ (v - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
      omega
    have hlit := M8.AntipodalFamily.literal_polynomial N h8 heven
    have hm := (M8.AntipodalFamily.nontrivial N h8 heven).1
    have hd : M8.AntipodalFamily.polynomial N ∣ M6.Cyclic.modulus N := by
      rw [hN]
      exact M8.AntipodalFamily.divides_modulus v hv
    have hs := (M7.RecipeSignature.signature_properties N (M8.AntipodalFamily.recipe N)).1
    have hleft : M7.RecipeSignature.signature (M8.AntipodalFamily.recipe N) ∣ M8.AntipodalFamily.polynomial N := by
      rw [← hlit]
      first
      | change gcd (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N))) (M6.Cyclic.modulus N) ∣ _
        exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
      | change gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M6.Cyclic.modulus N)) ∣ _
        exact gcd_dvd_left _ _
    have hright : M8.AntipodalFamily.polynomial N ∣ M7.RecipeSignature.signature (M8.AntipodalFamily.recipe N) := by
      first
      | change _ ∣ gcd (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N))) (M6.Cyclic.modulus N)
        rw [hlit]
        exact dvd_gcd (dvd_gcd dvd_rfl dvd_rfl) hd
      | change _ ∣ gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M6.Cyclic.modulus N))
        rw [hlit]
        exact dvd_gcd dvd_rfl (dvd_gcd dvd_rfl hd)
    exact?
