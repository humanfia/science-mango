import M5PolynomialIndicator
import M5PolynomialExclusionAccepted

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
