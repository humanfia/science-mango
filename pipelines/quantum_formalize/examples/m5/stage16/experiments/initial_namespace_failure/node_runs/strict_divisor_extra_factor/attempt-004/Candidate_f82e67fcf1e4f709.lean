import FrozenTarget_f82e67fcf1e4f709
theorem M5.PolynomialExclusion.strict_divisor_extra_factor : QuantumHarnessFrozenTarget := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hF hFG hG hGF
  have hF0 : F ≠ 0 := hF.ne_zero
  let Q := G / F
  have hGQ : G = F * Q := (EuclideanDomain.mul_div_cancel' hF0 hFG).symm
  have hQ0 : Q ≠ 0 := by
    intro hQ
    apply hG
    simpa [hQ] using hGQ
  have hQu : ¬ IsUnit Q := by
    rintro ⟨u, hu⟩
    have hGFdvd : G ∣ F := by
      refine ⟨↑(u⁻¹), ?_⟩
      rw [hGQ, ← hu, mul_assoc]
      simp
    apply hGF
    first
    | solve | apply M5.binary_dvd_antisymm <;> assumption
    | solve | apply M5.BinaryDivisibility.binary_dvd_antisymm <;> assumption
    | solve | apply M5.PolynomialExclusion.binary_dvd_antisymm <;> assumption
    | solve | apply binary_dvd_antisymm <;> assumption
    | solve | apply dvd_antisymm <;> assumption
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF0 hFG).mp hpQ⟩
