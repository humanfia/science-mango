import FrozenTarget_201194238cc06f76
theorem M5.PolynomialExclusion.strict_divisor_extra_factor : QuantumHarnessFrozenTarget := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hF hFG hG0 hGF
  let Q := G / F
  have hG : G = F * Q := (EuclideanDomain.mul_div_cancel' hF.ne_zero hFG).symm
  have hQ0 : Q ≠ 0 := by
    intro hQ
    apply hG0
    rw [hG, hQ, mul_zero]
  have hQu : ¬ IsUnit Q := by
    rintro ⟨u, hu⟩
    have hGFdvd : G ∣ F := by
      refine ⟨↑(u⁻¹), ?_⟩
      rw [hG, ← hu]
      simp [mul_assoc]
    apply hGF
    first
    | (apply M5.binary_dvd_antisymm <;> assumption)
    | (apply M5.BinaryDivisibility.binary_dvd_antisymm <;> assumption)
    | (apply M5.PolynomialExclusion.binary_dvd_antisymm <;> assumption)
    | exact dvd_antisymm hGFdvd hFG
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  refine ⟨p, hp, ?_⟩
  exact (M5.PolynomialExclusion.factor_dvd_quotient F G p hF.ne_zero hFG).mp hpQ
