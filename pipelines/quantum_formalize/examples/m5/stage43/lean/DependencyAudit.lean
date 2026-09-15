import M5ArithmeticWorkflowReady
example : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0 := @M5.PolynomialExclusion.cyclic_quotient_nonzero
#print axioms M5.PolynomialExclusion.cyclic_quotient_nonzero
example : ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P) := @M5.PolynomialExclusion.factor_dvd_quotient
#print axioms M5.PolynomialExclusion.factor_dvd_quotient
example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N := @M5.PolynomialExclusion.signature_contains
#print axioms M5.PolynomialExclusion.signature_contains
example : ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G := @M5.PolynomialExclusion.strict_divisor_extra_factor
#print axioms M5.PolynomialExclusion.strict_divisor_extra_factor
example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b)) := @M5.PolynomialExclusion.exact_signature_criterion
#print axioms M5.PolynomialExclusion.exact_signature_criterion
example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, ¬ (F * p ∣ a ∧ F * p ∣ b)) := @M5.PolynomialExclusion.finite_factor_criterion
#print axioms M5.PolynomialExclusion.finite_factor_criterion
example : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, p.Monic ∧ Irreducible p := @M5.PolynomialIndicator.residual_factors_regular
#print axioms M5.PolynomialIndicator.residual_factors_regular
example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := @M5.PolynomialIndicator.conditional_indicator
#print axioms M5.PolynomialIndicator.conditional_indicator
example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := @M5.PolynomialIndicator.exact_signature_indicator
#print axioms M5.PolynomialIndicator.exact_signature_indicator
example : ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U := @M5.AnchoredCount.anchor_polynomial
#print axioms M5.AnchoredCount.anchor_polynomial
example : ∀ (P : M5.BinaryPolynomial) (U : Finset ℕ), 0 ∉ U → (P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = 1) := @M5.AnchoredCount.anchor_divisibility
#print axioms M5.AnchoredCount.anchor_divisibility
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ), 0 ∉ W → M5.ArithmeticSubset.n P hP W k 1 = (M5.AnchoredCount.count P W k : ℤ) := @M5.AnchoredCount.anchored_single_block_count
#print axioms M5.AnchoredCount.anchored_single_block_count
example : ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N := @M5.OrderBoundary.range_card
#print axioms M5.OrderBoundary.range_card
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F A B → M5.signaturePeriod F ∣ N ∧ w ≤ N ∧ F.natDegree < N := @M5.OrderBoundary.signature_lower_bounds
#print axioms M5.OrderBoundary.signature_lower_bounds
example : ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0} := @M5.OrderBoundary.weight_one_iff
#print axioms M5.OrderBoundary.weight_one_iff
example : ∀ (T lower B : ℕ) (C : ℕ → ℤ), (∃ N : ℕ, N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ b ≤ B ∧ lower ≤ b ∧ T ∣ b ∧ 0 < C b ∧ ∀ N : ℕ, lower ≤ N → T ∣ N → 0 < C N → b ≤ N := @M5.BirthSearch.birth_spec
#print axioms M5.BirthSearch.birth_spec
example : ∀ (T lower B : ℕ) (C : ℕ → ℤ) (Valid : ℕ → Prop), (∀ N : ℕ, Valid N → lower ≤ N ∧ T ∣ N) → (∀ N : ℕ, lower ≤ N → T ∣ N → (0 < C N ↔ Valid N)) → (∃ N : ℕ, N ≤ B ∧ Valid N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ Valid b ∧ ∀ N : ℕ, Valid N → b ≤ N := @M5.BirthSearch.birth_exact
#print axioms M5.BirthSearch.birth_exact
example : ∀ (T lower B : ℕ) (C : ℕ → ℤ), M5.BirthSearch.birth T lower B C = none ↔ ∀ N : ℕ, N ≤ B → lower ≤ N → T ∣ N → C N ≤ 0 := @M5.BirthSearch.birth_none_iff
#print axioms M5.BirthSearch.birth_none_iff
