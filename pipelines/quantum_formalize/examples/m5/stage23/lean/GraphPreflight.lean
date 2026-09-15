import M5PolynomialIndicator

noncomputable def M5.Stage23Target.residual_factors_regular : Prop :=
  ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, p.Monic ∧ Irreducible p

#check M5.Stage23Target.residual_factors_regular

noncomputable def M5.Stage23Target.conditional_indicator : Prop :=
  ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0)

#check M5.Stage23Target.conditional_indicator

noncomputable def M5.Stage23Target.exact_signature_indicator : Prop :=
  ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0)

#check M5.Stage23Target.exact_signature_indicator

