import M5ArithmeticWorkflowReady
example : ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s) := @M5.OrderCount.divisor_subset_domain
#print axioms M5.OrderCount.divisor_subset_domain
example : ∀ (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ), P.Monic → 0 ∉ W → M5.OrderCount.nOne P W k ^ 2 = M5.OrderCount.twoBlockIndicatorSum P W k := @M5.OrderCount.two_block_divisibility_count
#print axioms M5.OrderCount.two_block_divisibility_count
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.rawC N w F = ∑ U ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), ∑ V ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), M5.OrderCount.pairIndicator N F U V := @M5.OrderCount.arithmetic_indicator_expansion
#print axioms M5.OrderCount.arithmetic_indicator_expansion
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card := @M5.OrderCount.exact_C
#print axioms M5.OrderCount.exact_C
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → 0 ≤ M5.OrderCount.C N w F := @M5.OrderCount.C_nonnegative
#print axioms M5.OrderCount.C_nonnegative
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → (0 < M5.OrderCount.C N w F ↔ ∃ A B : Finset ℕ, A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧ 0 ∈ A ∧ 0 ∈ B ∧ A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F) := @M5.OrderCount.C_positive_iff_realization
#print axioms M5.OrderCount.C_positive_iff_realization
example : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (S U : Finset ℕ), 0 < w → F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F S U → 0 < M5.ResidueCount.A w F := @M5.GlobalCriterion.physical_implies_A_positive
#print axioms M5.GlobalCriterion.physical_implies_A_positive
example : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U := @M5.GlobalCriterion.positive_bounded_progression
#print axioms M5.GlobalCriterion.positive_bounded_progression
example : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U) ∧ (M5.ResidueCount.A w F = 0 ↔ ¬ (∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U)) := @M5.GlobalCriterion.global_occurrence_criterion
#print axioms M5.GlobalCriterion.global_occurrence_criterion
