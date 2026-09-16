import FrozenTarget_5be08923572f1ea5
theorem M8.MixedFamily.signature : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  have hp := M8.MixedFamily.literal_polynomials N hN
  have hm := (M7.RecipeSignature.signature_properties N (M8.MixedFamily.recipe N)).1
  have ha : M8.MixedFamily.a.Monic := by
    simpa [M8.MixedFamily.a, add_comm] using
      (Polynomial.monic_X_add_C (1 : ZMod 2))
  have hab : M8.MixedFamily.a ∣ M8.MixedFamily.b := by
    rw [M8.MixedFamily.algebra.1]
    exact dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0)
  have hmod : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    have heq : M8.MixedFamily.a = Polynomial.X - Polynomial.C (1 : ZMod 2) := by
      norm_num [M8.MixedFamily.a, sub_eq_add_neg, add_comm]
    rw [heq]
    apply Polynomial.X_sub_C_dvd_iff.mpr
    simp [M6.Cyclic.modulus]
  apply hm.dvd_antisymm ha
  all_goals
    simp only [M7.RecipeSignature.signature, M8.MixedFamily.recipe,
      hp.1, hp.2]
  all_goals
    first
    | change gcd (gcd M8.MixedFamily.a M8.MixedFamily.b) (M6.Cyclic.modulus N) ∣ M8.MixedFamily.a
      exact (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)
    | change M8.MixedFamily.a ∣ gcd (gcd M8.MixedFamily.a M8.MixedFamily.b) (M6.Cyclic.modulus N)
      exact dvd_gcd (dvd_gcd dvd_rfl hab) hmod
    | change gcd M8.MixedFamily.a (gcd M8.MixedFamily.b (M6.Cyclic.modulus N)) ∣ M8.MixedFamily.a
      exact gcd_dvd_left _ _
    | change M8.MixedFamily.a ∣ gcd M8.MixedFamily.a (gcd M8.MixedFamily.b (M6.Cyclic.modulus N))
      exact dvd_gcd dvd_rfl (dvd_gcd hab hmod)
