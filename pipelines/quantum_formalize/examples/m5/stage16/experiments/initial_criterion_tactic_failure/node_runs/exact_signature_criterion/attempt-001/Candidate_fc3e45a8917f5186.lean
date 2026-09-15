import FrozenTarget_fc3e45a8917f5186
theorem M5.PolynomialExclusion.exact_signature_criterion : QuantumHarnessFrozenTarget := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b))
  intro a b F N hN hFm hFP hFa hFb
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hparts : M5.completeSignature a b N ∣ a ∧ M5.completeSignature a b N ∣ b ∧ M5.completeSignature a b N ∣ M5.cyclicModulus N := by
    unfold M5.completeSignature
    refine ⟨?_, ?_, ?_⟩
    all_goals first
      | exact EuclideanDomain.gcd_dvd_left _ _
      | exact EuclideanDomain.gcd_dvd_right _ _
      | exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
      | exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
      | exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_left _ _)
      | exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_right _ _)
  constructor
  · intro hEq p hp hpQ ⟨hpa, hpb⟩
    have hpP : F * p ∣ M5.cyclicModulus N :=
      (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N) p hF0 hFP).mp hpQ
    have hpF : F * p ∣ F := by
      rw [← hEq]
      exact M5.PolynomialExclusion.signature_contains a b (F * p) N hpa hpb hpP
    obtain ⟨q, hq⟩ := hpF
    have hone : (1 : M5.BinaryPolynomial) = p * q := by
      apply mul_left_cancel₀ hF0
      simpa only [mul_one, mul_assoc] using hq
    exact hp.not_isUnit (isUnit_iff_dvd_one.mpr ⟨q, hone⟩)
  · intro hExclude
    have hP0 : M5.cyclicModulus N ≠ 0 := by
      intro hz
      have hc := congrArg (fun q : M5.BinaryPolynomial => q.coeff N) hz
      simpa [M5.cyclicModulus, hN.ne', hN.ne] using hc
    have hG0 : M5.completeSignature a b N ≠ 0 := by
      intro hz
      apply hP0
      exact zero_dvd_iff.mp (hz ▸ hparts.2.2)
    have hFG := M5.PolynomialExclusion.signature_contains a b F N hFa hFb hFP
    by_contra hne
    obtain ⟨p, hp, hpG⟩ := M5.PolynomialExclusion.strict_divisor_extra_factor F (M5.completeSignature a b N) hFm hFG hG0 hne
    have hpP := dvd_trans hpG hparts.2.2
    have hpQ := (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N) p hF0 hFP).mpr hpP
    exact hExclude p hp hpQ ⟨dvd_trans hpG hparts.1, dvd_trans hpG hparts.2.1⟩
