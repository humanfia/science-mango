import FrozenTarget_7d544c3016fc9224
theorem M5.PolynomialExclusion.strict_divisor_extra_factor : QuantumHarnessFrozenTarget := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hF hFG hG0 hGF
  have hG : G = F * (G / F) :=
    (EuclideanDomain.mul_div_cancel' hF.ne_zero hFG).symm
  have hQ0 : G / F ≠ 0 := by
    intro hQ
    apply hG0
    simp [hQ] at hG
    exact hG
  have hQu : ¬ IsUnit (G / F) := by
    intro hu
    rcases hu with ⟨u, hu⟩
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
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF.ne_zero hFG).mp hpQ⟩
