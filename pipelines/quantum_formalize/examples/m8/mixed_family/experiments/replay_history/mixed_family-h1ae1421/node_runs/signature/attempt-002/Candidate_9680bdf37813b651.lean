import FrozenTarget_9680bdf37813b651
theorem M8.MixedFamily.signature : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  obtain ⟨hleft, hright⟩ := M8.MixedFamily.literal_polynomials N hN
  have ha : M8.MixedFamily.a.Monic := by
    simpa [M8.MixedFamily.a, add_comm] using (Polynomial.monic_X_add_C (1 : ZMod 2))
  have hab : M8.MixedFamily.a ∣ M8.MixedFamily.b := by
    rw [M8.MixedFamily.algebra.1]
    exact dvd_pow_self _ (by decide : 2 ≠ 0)
  have hn : (-1 : ZMod 2) = 1 := by decide
  have hm : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    have hr : Polynomial.IsRoot (M6.Cyclic.modulus N) (-1 : ZMod 2) := by
      simp [Polynomial.IsRoot, M6.Cyclic.modulus, hn]
      <;> decide
    have hd := Polynomial.dvd_iff_isRoot.mpr hr
    simpa [M8.MixedFamily.a, sub_eq_add_neg, ← Polynomial.C_neg, add_comm] using hd
  have hs := (M7.RecipeSignature.signature_properties N (M8.MixedFamily.recipe N)).1
  have hsa : M7.RecipeSignature.signature (M8.MixedFamily.recipe N) ∣ M8.MixedFamily.a := by
    unfold M7.RecipeSignature.signature M6.Cyclic.signature
    dsimp only [M8.MixedFamily.recipe]
    rw [hleft, hright]
    first
    | exact gcd_dvd_left _ _
    | exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
    | exact dvd_trans (gcd_dvd_right _ _) (gcd_dvd_left _ _)
  have has : M8.MixedFamily.a ∣ M7.RecipeSignature.signature (M8.MixedFamily.recipe N) := by
    unfold M7.RecipeSignature.signature M6.Cyclic.signature
    dsimp only [M8.MixedFamily.recipe]
    rw [hleft, hright]
    repeat' apply dvd_gcd
    all_goals first | exact dvd_refl _ | exact hab | exact hm
  have hdeg := Polynomial.natDegree_le_of_dvd hsa ha.ne_zero
  have heq := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le ha has hdeg
  simpa only [hs, Polynomial.C_1, one_mul] using heq
