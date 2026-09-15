import FrozenTarget_5073736e8134bc06
theorem M5.PolynomialExclusion.exact_signature_criterion : QuantumHarnessFrozenTarget := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b))
  intro a b F N hN hFm hFM hFa hFb
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hdiv : M5.completeSignature a b N ∣ a ∧ M5.completeSignature a b N ∣ b ∧ M5.completeSignature a b N ∣ M5.cyclicModulus N := by
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
  constructor
  · intro hEq p hp hpQ hab
    have hpM : F * p ∣ M5.cyclicModulus N :=
      (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N) p hF0 hFM).mp hpQ
    have hpS := M5.PolynomialExclusion.signature_contains a b (F * p) N hab.1 hab.2 hpM
    rw [hEq] at hpS
    have hpFF : p ∣ F / F :=
      (M5.PolynomialExclusion.factor_dvd_quotient F F p hF0 dvd_rfl).mpr hpS
    have hp1 : p ∣ 1 := by
      simpa only [EuclideanDomain.div_self hF0] using hpFF
    exact hp.not_unit (isUnit_of_dvd_one hp1)
  · intro hexcl
    have hM0 : M5.cyclicModulus N ≠ 0 := by
      intro hz
      have hc := congrArg (fun q : M5.BinaryPolynomial => q.coeff N) hz
      simpa [M5.cyclicModulus, Polynomial.coeff_X_pow, Nat.ne_of_gt hN] using hc
    have hS0 : M5.completeSignature a b N ≠ 0 := by
      intro hz
      apply hM0
      have hd := hdiv.2.2
      rw [hz] at hd
      exact zero_dvd_iff.mp hd
    have hFS := M5.PolynomialExclusion.signature_contains a b F N hFa hFb hFM
    by_contra hne
    obtain ⟨p, hp, hpS⟩ := M5.PolynomialExclusion.strict_divisor_extra_factor F (M5.completeSignature a b N) hFm hFS hS0 hne
    have hpM := dvd_trans hpS hdiv.2.2
    have hpQ := (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N) p hF0 hFM).mpr hpM
    exact hexcl p hp hpQ ⟨dvd_trans hpS hdiv.1, dvd_trans hpS hdiv.2.1⟩
