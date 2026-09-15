import FrozenTarget_a9746cffe6c51d6f
theorem M5.PolynomialIndicator.exact_signature_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0)
  intro a b F N hN hF hdiv
  by_cases hab : F ∣ a ∧ F ∣ b
  · exact M5.PolynomialIndicator.conditional_indicator a b F N hN hF hdiv hab.1 hab.2
  · have hne : M5.completeSignature a b N ≠ F := by
      intro he
      have hd : F ∣ M5.completeSignature a b N := by
        rw [he]
      simp only [M5.completeSignature, EuclideanDomain.dvd_gcd_iff] at hd
      tauto
    have hbad : ∀ P : M5.BinaryPolynomial, ¬ (F * P ∣ a ∧ F * P ∣ b) := by
      intro P hP
      exact hab ⟨dvd_trans (dvd_mul_right F P) hP.1,
        dvd_trans (dvd_mul_right F P) hP.2⟩
    rw [if_neg hne]
    unfold M5.PolynomialIndicator.factorExclusionSum
    apply Finset.sum_eq_zero
    intro H hH
    simp [hbad]
