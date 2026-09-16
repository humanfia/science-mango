import FrozenTarget_9835ca7daefac166
theorem M8.AntipodalFamily.signature : QuantumHarnessFrozenTarget := by
    classical
    intro N inst v hv hN
    have hpow : 2 ^ v = 2 ^ (v - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
    have hlarge : 8 ≤ N := by
      rw [hN]
      calc
        8 = (2 : ℕ) ^ 3 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
    have heven : Even N := by
      refine ⟨2 ^ (v - 1), ?_⟩
      omega
    have hlit := M8.AntipodalFamily.literal_polynomial N hlarge heven
    have hm := (M8.AntipodalFamily.nontrivial N hlarge heven).1
    have hd : M8.AntipodalFamily.polynomial N ∣ M6.Cyclic.modulus N := by
      rw [hN]
      exact M8.AntipodalFamily.divides_modulus v hv
    have hs := (M7.RecipeSignature.signature_properties N (M8.AntipodalFamily.recipe N)).1
    apply Polynomial.Monic.dvd_antisymm hs hm
    · first
      | change gcd (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N))) (M6.Cyclic.modulus N) ∣ _
      | change gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M6.Cyclic.modulus N)) ∣ _
      | change gcd (M6.Cyclic.modulus N) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N))) ∣ _
      rw [hlit]
      first
      | exact gcd_dvd_left _ _
      | exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
      | exact dvd_trans (gcd_dvd_right _ _) (gcd_dvd_left _ _)
    · first
      | change _ ∣ gcd (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N))) (M6.Cyclic.modulus N)
      | change _ ∣ gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M6.Cyclic.modulus N))
      | change _ ∣ gcd (M6.Cyclic.modulus N) (gcd (M7.Supports.polynomial (M8.AntipodalFamily.support N)) (M7.Supports.polynomial (M8.AntipodalFamily.support N)))
      rw [hlit]
      repeat' apply dvd_gcd
      all_goals first | exact dvd_refl _ | exact hd
