import FrozenTarget_ee1aa4627e502734
theorem M8.MixedFamily.signature : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  obtain ⟨hleft, hright⟩ := M8.MixedFamily.literal_polynomials N hN
  have ha : M8.MixedFamily.a.Monic := by
    simpa [M8.MixedFamily.a, add_comm] using
      (Polynomial.monic_X_add_C (1 : ZMod 2))
  have hab : M8.MixedFamily.a ∣ M8.MixedFamily.b := by
    refine ⟨M8.MixedFamily.a, ?_⟩
    rw [M8.MixedFamily.algebra.1, pow_two]
  have ham : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    have hd : (Polynomial.X - Polynomial.C (1 : ZMod 2)) ∣ M6.Cyclic.modulus N := by
      apply Polynomial.dvd_iff_isRoot.mpr
      simp [Polynomial.IsRoot, M6.Cyclic.modulus]
    have hn : -(1 : ZMod 2) = 1 := by decide
    change (1 + Polynomial.X : Polynomial (ZMod 2)) ∣ M6.Cyclic.modulus N
    simpa only [sub_eq_add_neg, ← Polynomial.C_neg, hn, Polynomial.C_1, add_comm] using hd
  have hg (p : Polynomial (ZMod 2)) (hp : M8.MixedFamily.a ∣ p) :
      gcd M8.MixedFamily.a p = M8.MixedFamily.a := by
    first
    | exact Polynomial.gcd_eq_left ha hp
    | exact ha.gcd_eq_left hp
    | simpa only [ha.normalize_eq] using (gcd_eq_left hp)
    | apply ha.dvd_antisymm
      · exact?
      · exact gcd_dvd_left _ _
      · exact dvd_gcd (dvd_refl _) hp
  unfold M7.RecipeSignature.signature
  first
  | change gcd (gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
      (M7.Supports.polynomial (M8.MixedFamily.right N))) (M6.Cyclic.modulus N) = M8.MixedFamily.a
    rw [hleft, hright, hg _ hab, hg _ ham]
  | change gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
      (gcd (M7.Supports.polynomial (M8.MixedFamily.right N)) (M6.Cyclic.modulus N)) = M8.MixedFamily.a
    rw [hleft, hright]
    exact hg _ (dvd_gcd hab ham)
  | change gcd (M6.Cyclic.modulus N)
      (gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
        (M7.Supports.polynomial (M8.MixedFamily.right N))) = M8.MixedFamily.a
    rw [hleft, hright, hg _ hab, gcd_comm, hg _ ham]
