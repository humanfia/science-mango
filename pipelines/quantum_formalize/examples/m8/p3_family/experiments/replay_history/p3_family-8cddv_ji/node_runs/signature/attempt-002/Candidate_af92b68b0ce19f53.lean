import FrozenTarget_af92b68b0ce19f53
theorem M8.P3Family.signature : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M7.RecipeSignature.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial
  intro N inst hN hdiv
  have hp := M8.P3Family.literal_polynomial N hN
  have hd := M8.P3Family.divides_modulus N hdiv
  have hm : M8.P3Family.polynomial.Monic := by
    unfold M8.P3Family.polynomial
    monicity <;> norm_num
  have hs := (M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)).1
  have hsp : M7.RecipeSignature.signature (M8.P3Family.recipe N) ∣ M8.P3Family.polynomial := by
    dsimp [M7.RecipeSignature.signature, M8.P3Family.recipe]
    rw [hp]
    first
    | exact gcd_dvd_left _ _
    | exact dvd_trans (gcd_dvd_left _ _) (gcd_dvd_left _ _)
    | exact dvd_trans (gcd_dvd_right _ _) (gcd_dvd_left _ _)
  have hps : M8.P3Family.polynomial ∣ M7.RecipeSignature.signature (M8.P3Family.recipe N) := by
    dsimp [M7.RecipeSignature.signature, M8.P3Family.recipe]
    rw [hp]
    simp only [dvd_gcd_iff]
    aesop
  first
  | exact Polynomial.dvd_antisymm hs hm hsp hps
  | exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hs hm hsp (Polynomial.natDegree_le_of_dvd hps hs.ne_zero)
  | exact Polynomial.eq_of_monic_of_associated hs hm (associated_of_dvd_dvd hsp hps)
