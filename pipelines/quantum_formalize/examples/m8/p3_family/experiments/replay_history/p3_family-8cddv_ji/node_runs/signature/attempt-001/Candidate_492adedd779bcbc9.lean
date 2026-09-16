import FrozenTarget_492adedd779bcbc9
theorem M8.P3Family.signature : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M7.RecipeSignature.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial
  intro N inst hN hdiv
  have hp := M8.P3Family.literal_polynomial N hN
  have hd := M8.P3Family.divides_modulus N hdiv
  have hm : M8.P3Family.polynomial.Monic := by
    unfold M8.P3Family.polynomial
    monicity
  have hs := (M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)).1
  apply hs.dvd_antisymm hm
  all_goals
    dsimp [M7.RecipeSignature.signature, M8.P3Family.recipe]
    simp only [hp]
  first
  | change gcd (gcd M8.P3Family.polynomial M8.P3Family.polynomial) (M6.Cyclic.modulus N) ∣ M8.P3Family.polynomial
    exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  | change gcd M8.P3Family.polynomial (gcd M8.P3Family.polynomial (M6.Cyclic.modulus N)) ∣ M8.P3Family.polynomial
    exact gcd_dvd_left _ _
  first
  | change M8.P3Family.polynomial ∣ gcd (gcd M8.P3Family.polynomial M8.P3Family.polynomial) (M6.Cyclic.modulus N)
    exact dvd_gcd (dvd_gcd (dvd_refl _) (dvd_refl _)) hd
  | change M8.P3Family.polynomial ∣ gcd M8.P3Family.polynomial (gcd M8.P3Family.polynomial (M6.Cyclic.modulus N))
    exact dvd_gcd (dvd_refl _) (dvd_gcd (dvd_refl _) hd)
