import FrozenTarget_2b4e269fe9d33735
theorem M5.PolynomialExclusion.exact_signature_criterion : QuantumHarnessFrozenTarget := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b))
  intro a b F N hN hFm hFN hFa hFb
  have hF0 : F ≠ 0 := hFm.ne_zero
  constructor
  · intro heq p hp hpQ hab
    have hpN : F * p ∣ M5.cyclicModulus N :=
      (M5.PolynomialExclusion.factor_dvd_quotient F _ p hF0 hFN).mp hpQ
    have hpF : F * p ∣ F := by
      rw [← heq]
      exact M5.PolynomialExclusion.signature_contains a b (F * p) N hab.1 hab.2 hpN
    obtain ⟨q, hq⟩ := hpF
    have hcancel : (1 : M5.BinaryPolynomial) = p * q := by
      apply mul_left_cancel₀ hF0
      simpa only [mul_one, mul_assoc] using hq
    exact hp.not_isUnit (isUnit_iff_dvd_one.mpr ⟨q, hcancel⟩)
  · intro hexclude
    have hdiv : M5.completeSignature a b N ∣ a ∧
        M5.completeSignature a b N ∣ b ∧
        M5.completeSignature a b N ∣ M5.cyclicModulus N := by
      unfold M5.completeSignature
      refine ⟨?_, ?_, ?_⟩
      all_goals
        first
        | exact EuclideanDomain.gcd_dvd_left _ _
        | exact EuclideanDomain.gcd_dvd_right _ _
        | exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
        | exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
        | exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_left _ _)
        | exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_right _ _)
    have hM0 : M5.cyclicModulus N ≠ 0 := by
      intro hz
      have hc := congrArg (fun f : M5.BinaryPolynomial => f.coeff N) hz
      simpa [M5.cyclicModulus, ne_of_gt hN] using hc
    have hG0 : M5.completeSignature a b N ≠ 0 := by
      intro hz
      apply hM0
      exact zero_dvd_iff.mp (hz ▸ hdiv.2.2)
    have hFG : F ∣ M5.completeSignature a b N :=
      M5.PolynomialExclusion.signature_contains a b F N hFa hFb hFN
    by_contra hne
    obtain ⟨p, hp, hpG⟩ :=
      M5.PolynomialExclusion.strict_divisor_extra_factor F _ hFm hFG hG0 hne
    have hpQ : p ∣ M5.cyclicModulus N / F :=
      (M5.PolynomialExclusion.factor_dvd_quotient F _ p hF0 hFN).mpr
        (dvd_trans hpG hdiv.2.2)
    exact hexclude p hp hpQ ⟨dvd_trans hpG hdiv.1, dvd_trans hpG hdiv.2.1⟩
