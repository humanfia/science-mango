import FrozenTarget_a69c752088316e79
theorem M8.AntipodalFamily.signature : QuantumHarnessFrozenTarget := by
    classical
    intro N inst v hv hNv
    have hN : 8 ≤ N := by
      rw [hNv]
      have h : (2 : ℕ) ^ 3 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv
      norm_num at h ⊢
      exact h
    have hp : 2 ^ v = 2 ^ (v - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
    have hEven : Even N := by
      refine ⟨2 ^ (v - 1), ?_⟩
      rw [hNv, hp]
      omega
    have hl := M8.AntipodalFamily.literal_polynomial N hN hEven
    have hm := (M8.AntipodalFamily.nontrivial N hN hEven).1
    have hd : M8.AntipodalFamily.polynomial N ∣ M6.Cyclic.modulus N := by
      rw [hNv]
      exact M8.AntipodalFamily.divides_modulus v hv
    let p := M8.AntipodalFamily.polynomial N
    have hn : normalize p = p := hm.normalize_eq_self
    have hg : gcd p (M6.Cyclic.modulus N) = p := by
      rw [gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl _) hd), hn]
    have he : EuclideanDomain.gcd p (M6.Cyclic.modulus N) = p :=
      EuclideanDomain.gcd_eq_left.mpr hd
    have heSelf : EuclideanDomain.gcd p p = p :=
      EuclideanDomain.gcd_eq_left.mpr (dvd_refl _)
    unfold M7.RecipeSignature.signature M8.AntipodalFamily.recipe
    simp only [hl]
    unfold M6.Cyclic.signature
    first
    | simpa only [← show M8.AntipodalFamily.polynomial N = p from rfl,
        gcd_self, hn, hg, heSelf, he]
    | simpa only [← show M8.AntipodalFamily.polynomial N = p from rfl,
        gcd_self, hn, gcd_comm (M6.Cyclic.modulus N) p, hg, heSelf, he]
