import M5PolynomialIndicator

theorem M5.PolynomialExclusion.cyclic_quotient_nonzero : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0 := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0
  intro F N hN hmonic hdvd hquot
  have hmul := EuclideanDomain.mul_div_cancel' hmonic.ne_zero hdvd
  have hzero : M5.cyclicModulus N = 0 := by
    rw [hquot, mul_zero] at hmul
    exact hmul.symm
  have hcoeff := congrArg (fun p : M5.BinaryPolynomial => p.coeff N) hzero
  simp [M5.cyclicModulus, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, Nat.ne_of_gt hN] at hcoeff

theorem M5.PolynomialExclusion.factor_dvd_quotient : ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P) := by
  change ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P)
  intro F P p hF hFP
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      P = F * (P / F) := (EuclideanDomain.mul_div_cancel' hF hFP).symm
      _ = F * (p * q) := congrArg (fun x => F * x) hq
      _ = (F * p) * q := (mul_assoc F p q).symm
  · intro h
    exact EuclideanDomain.dvd_div_of_mul_dvd h

theorem M5.PolynomialExclusion.signature_contains : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N
  intro a b F N ha hb hN
  unfold M5.completeSignature
  repeat' first | assumption | apply EuclideanDomain.dvd_gcd

theorem M5.PolynomialExclusion.strict_divisor_extra_factor : ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G := by
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
    exact M5.Signature.binary_dvd_antisymm G F hGF hFG
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF0 hFG).mp hpQ⟩

theorem M5.PolynomialExclusion.exact_signature_criterion : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b)) := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b))
  intro a b F N hN hFm hFM hFa hFb
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hdiv : M5.completeSignature a b N ∣ a ∧ M5.completeSignature a b N ∣ b ∧ M5.completeSignature a b N ∣ M5.cyclicModulus N := by
    change EuclideanDomain.gcd (EuclideanDomain.gcd a b) (M5.cyclicModulus N) ∣ a ∧ EuclideanDomain.gcd (EuclideanDomain.gcd a b) (M5.cyclicModulus N) ∣ b ∧ EuclideanDomain.gcd (EuclideanDomain.gcd a b) (M5.cyclicModulus N) ∣ M5.cyclicModulus N
    have hleft := EuclideanDomain.gcd_dvd_left (EuclideanDomain.gcd a b) (M5.cyclicModulus N)
    exact ⟨dvd_trans hleft (EuclideanDomain.gcd_dvd_left a b), dvd_trans hleft (EuclideanDomain.gcd_dvd_right a b), EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd a b) (M5.cyclicModulus N)⟩
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
    exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hp1)
  · intro hexcl
    have hM0 : M5.cyclicModulus N ≠ 0 := by
      intro hz
      have hc := congrArg (fun q : M5.BinaryPolynomial => q.coeff N) hz
      simpa [M5.cyclicModulus, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one, Nat.ne_of_gt hN] using hc
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

theorem M5.PolynomialExclusion.finite_factor_criterion : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, ¬ (F * p ∣ a ∧ F * p ∣ b)) := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, ¬ (F * p ∣ a ∧ F * p ∣ b))
  intro a b F N hN hFm hFM hFa hFb
  classical
  rw [M5.PolynomialExclusion.exact_signature_criterion a b F N hN hFm hFM hFa hFb]
  constructor
  · intro h p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
      simpa [M5.PolynomialExclusion.residualFactors] using hp
    exact h p (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hp')
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp')
  · intro h p hp hpQ hab
    have hQ : M5.cyclicModulus N / F ≠ 0 :=
      M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hFm hFM
    have hex : ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F), Associated p q := by
      apply UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd <;> assumption
    obtain ⟨q, hq, hpq⟩ := hex
    have hqmem : q ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F := by
      simpa [M5.PolynomialExclusion.residualFactors] using hq
    have hmul : F * q ∣ F * p := mul_dvd_mul (dvd_refl F) hpq.symm.dvd
    exact h q hqmem ⟨dvd_trans hmul hab.1, dvd_trans hmul hab.2⟩

theorem M5.PolynomialIndicator.residual_factors_regular : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, p.Monic ∧ Irreducible p := by
  classical
  intro F N hN hF hdiv p hp
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hmem : p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
    simpa [M5.PolynomialExclusion.residualFactors, hq] using hp
  have hirr : Irreducible p :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hmem
  exact ⟨M5.Signature.binary_monic p hirr.ne_zero, hirr⟩

theorem M5.PolynomialIndicator.conditional_indicator : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := by
  classical
  intro a b F N hN hF hdiv ha hb
  have hcrit := M5.PolynomialExclusion.finite_factor_criterion a b F N hN hF hdiv ha hb
  have hbad :
      (∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F,
        decide (F * p ∣ a ∧ F * p ∣ b) = false) ↔
        M5.completeSignature a b N = F := by
    simpa using hcrit.symm
  calc
    M5.PolynomialIndicator.factorExclusionSum a b F N =
        M5.FiniteExclusion.exclusionSum
          (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F)
          (fun p => decide (F * p ∣ a ∧ F * p ∣ b)) := by
      unfold M5.PolynomialIndicator.factorExclusionSum M5.FiniteExclusion.exclusionSum
      apply Finset.sum_congr rfl
      intro H hH
      have hreg : ∀ p ∈ H, p.Monic ∧ Irreducible p := by
        intro p hp
        exact M5.PolynomialIndicator.residual_factors_regular F N hN hF hdiv p
          ((Finset.mem_powerset.mp hH) hp)
      have hpa := M5.FactorProduct.product_event_iff H F a hF.ne_zero ha hreg
      have hpb := M5.FactorProduct.product_event_iff H F b hF.ne_zero hb hreg
      simp [hpa, hpb, forall_and]
    _ = (if M5.completeSignature a b N = F then 1 else 0) := by
      simpa only [hbad] using
        M5.FiniteExclusion.exclusion_indicator
          (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F)
          (fun p => decide (F * p ∣ a ∧ F * p ∣ b))

theorem M5.PolynomialIndicator.exact_signature_indicator : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := by
  classical
  intro a b F N hN hF hdiv
  by_cases hab : F ∣ a ∧ F ∣ b
  · exact M5.PolynomialIndicator.conditional_indicator a b F N hN hF hdiv hab.1 hab.2
  · have hne : M5.completeSignature a b N ≠ F := by
      intro he
      have hd : F ∣ EuclideanDomain.gcd a b := by
        rw [← he]
        exact EuclideanDomain.gcd_dvd_left _ _
      exact hab ⟨hd.trans (EuclideanDomain.gcd_dvd_left a b),
        hd.trans (EuclideanDomain.gcd_dvd_right a b)⟩
    rw [if_neg hne]
    unfold M5.PolynomialIndicator.factorExclusionSum
    apply Finset.sum_eq_zero
    intro H hH
    have hbad : ¬ (F * (∏ p ∈ H, p) ∣ a ∧ F * (∏ p ∈ H, p) ∣ b) := by
      intro h
      exact hab ⟨(dvd_mul_right F _).trans h.1,
        (dvd_mul_right F _).trans h.2⟩
    simp [hbad]
