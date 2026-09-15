import FrozenTarget_948285eef03e95c9
theorem M5.PolynomialExclusion.strict_divisor_extra_factor : QuantumHarnessFrozenTarget := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hF hFG hG0 hGF
  have hF0 : F ≠ 0 := hF.ne_zero
  have hG : G = F * (G / F) := (EuclideanDomain.mul_div_cancel' hF0 hFG).symm
  have hQ0 : G / F ≠ 0 := by
    intro hQ
    apply hG0
    simpa [hQ] using hG
  have hQunit : ¬ IsUnit (G / F) := by
    rintro ⟨u, hu⟩
    have hGFdvd : G ∣ F := by
      refine ⟨↑(u⁻¹), ?_⟩
      rw [hG, ← hu, mul_assoc]
      simp
    apply hGF
    first
    | apply M5.binary_dvd_antisymm <;> assumption
    | apply M5.BinaryDivisibility.binary_dvd_antisymm <;> assumption
    | apply M5.PolynomialExclusion.binary_dvd_antisymm <;> assumption
    | apply binary_dvd_antisymm <;> assumption
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQunit hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF0 hFG).mp hpQ⟩
