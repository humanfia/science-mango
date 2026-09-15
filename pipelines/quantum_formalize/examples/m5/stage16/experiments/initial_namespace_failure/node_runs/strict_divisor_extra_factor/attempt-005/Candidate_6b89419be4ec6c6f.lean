import FrozenTarget_6b89419be4ec6c6f
theorem M5.PolynomialExclusion.strict_divisor_extra_factor : QuantumHarnessFrozenTarget := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hFm hFG hG0 hGFne
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hG : G = F * (G / F) :=
    (EuclideanDomain.mul_div_cancel' hF0 hFG).symm
  have hQ0 : G / F ≠ 0 := by
    intro hQ
    apply hG0
    rw [hG, hQ, mul_zero]
  have hQu : ¬ IsUnit (G / F) := by
    rintro ⟨u, hu⟩
    have hGF : G ∣ F := by
      refine ⟨↑(u⁻¹), ?_⟩
      rw [hG, ← hu]
      simp [mul_assoc]
    apply hGFne
    solve
    | apply M5.BinaryDivisibility.binary_dvd_antisymm <;> assumption
    | apply M5.binary_dvd_antisymm <;> assumption
    | apply M5.PolynomialExclusion.binary_dvd_antisymm <;> assumption
    | apply binary_dvd_antisymm <;> assumption
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF0 hFG).mp hpQ⟩
