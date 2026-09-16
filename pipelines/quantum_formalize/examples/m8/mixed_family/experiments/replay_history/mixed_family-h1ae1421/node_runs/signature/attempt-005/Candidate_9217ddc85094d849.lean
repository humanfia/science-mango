import FrozenTarget_9217ddc85094d849
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
    exact dvd_pow_self _ (by decide : 2 ≠ 0)
  have hn : -(1 : Polynomial (ZMod 2)) = 1 := by
    have h := congrArg (fun c : ZMod 2 => Polynomial.C c)
      (show -(1 : ZMod 2) = 1 by decide)
    simpa using h
  have ham : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    simpa [M8.MixedFamily.a, M6.Cyclic.modulus, sub_eq_add_neg, hn, add_comm] using
      (sub_dvd_pow_sub_pow (Polynomial.X : Polynomial (ZMod 2)) 1 N)
  have hs : M7.RecipeSignature.signature (M8.MixedFamily.recipe N) =
      Polynomial.gcd (Polynomial.gcd M8.MixedFamily.a M8.MixedFamily.b)
        (M6.Cyclic.modulus N) := by
    change Polynomial.gcd
      (Polynomial.gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
        (M7.Supports.polynomial (M8.MixedFamily.right N)))
      (M6.Cyclic.modulus N) = _
    rw [hp.1, hp.2]
  have hsa : M7.RecipeSignature.signature (M8.MixedFamily.recipe N) ∣ M8.MixedFamily.a := by
    rw [hs]
    exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have has : M8.MixedFamily.a ∣ M7.RecipeSignature.signature (M8.MixedFamily.recipe N) := by
    rw [hs]
    exact dvd_gcd (dvd_gcd (dvd_refl _) hab) ham
  first
  | exact Polynomial.eq_of_monic_of_dvd_of_dvd hm ha hsa has
  | exact Polynomial.dvd_antisymm hm ha hsa has
  | exact?
