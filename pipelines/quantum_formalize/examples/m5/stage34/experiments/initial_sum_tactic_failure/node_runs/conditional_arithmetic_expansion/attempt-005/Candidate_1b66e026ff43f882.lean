import FrozenTarget_1b66e026ff43f882
theorem M5.ConditionalCount.conditional_arithmetic_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFd hOK
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hAr (d : ℕ) : Disjoint A (M5.ConditionalCount.restricted WA d) :=
    hA.mono_right (Finset.filter_subset _ _)
  have hBr (d : ℕ) : Disjoint B (M5.ConditionalCount.restricted WB d) :=
    hB.mono_right (Finset.filter_subset _ _)
  have hmonic : ∀ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
      (F * ∏ p ∈ S, p).Monic := by
    intro S hS
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFd p
      ((Finset.mem_powerset.mp hS) hp)).1
  have hite {ι : Type*} (p : Prop) [Decidable p] (s : Finset ι) (f : ι → ℤ) :
      (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
    by_cases hp : p <;> simp [hp]
  have hcount (d : ℕ) (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      M5.ConditionalCount.nSelected (F * ∏ p ∈ S, p) A
          (M5.ConditionalCount.restricted WA d) (w - A.card) *
        M5.ConditionalCount.nSelected (F * ∏ p ∈ S, p) B
          (M5.ConditionalCount.restricted WB d) (w - B.card) =
        ∑ U ∈ WA.powersetCard (w - A.card),
          ∑ V ∈ WB.powersetCard (w - B.card),
            if (∀ s ∈ U, d ∣ s) ∧ (∀ s ∈ V, d ∣ s) then
              (if (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ∧
                  (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (B ∪ V)
                then (1 : ℤ) else 0)
            else 0 := by
    rw [M5.ConditionalCount.two_block_completion_count _ _ _ _ _ _ _
      (hmonic S hS) (hAr d) (hBr d)]
    unfold M5.ConditionalCount.twoBlockIndicatorSum
    rw [M5.ConditionalCount.restricted_subset_domain,
      M5.ConditionalCount.restricted_subset_domain]
    simp only [Finset.sum_filter]
    simp_rw [hite]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    by_cases hu : ∀ s ∈ U, d ∣ s <;>
      by_cases hv : ∀ s ∈ V, d ∣ s <;> simp [hu, hv]
  have hdU (f : ℕ → Finset ℕ → ℤ) :
      (∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
        ∑ U ∈ WA.powersetCard (w - A.card), f d U) =
      ∑ U ∈ WA.powersetCard (w - A.card),
        ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors, f d U :=
    Finset.sum_comm
  have hdV (f : ℕ → Finset ℕ → ℤ) :
      (∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
        ∑ V ∈ WB.powersetCard (w - B.card), f d V) =
      ∑ V ∈ WB.powersetCard (w - B.card),
        ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors, f d V :=
    Finset.sum_comm
  have hsU (f : Finset M5.BinaryPolynomial → Finset ℕ → ℤ) :
      (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        ∑ U ∈ WA.powersetCard (w - A.card), f S U) =
      ∑ U ∈ WA.powersetCard (w - A.card),
        ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
          f S U := Finset.sum_comm
  have hsV (f : Finset M5.BinaryPolynomial → Finset ℕ → ℤ) :
      (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        ∑ V ∈ WB.powersetCard (w - B.card), f S V) =
      ∑ V ∈ WB.powersetCard (w - B.card),
        ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
          f S V := Finset.sum_comm
  have hsd (f : Finset M5.BinaryPolynomial → ℕ → ℤ) :
      (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors, f S d) =
      ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
        ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
          f S d := Finset.sum_comm
  simp only [M5.ConditionalCount.rawCompletion, mul_assoc, hcount]
  simp only [M5.ConditionalCount.pairIndicator,
    M5.ConditionalCount.selectedDivisorSum,
    M5.PolynomialIndicator.factorExclusionSum]
  simp only [Finset.mul_sum, Finset.sum_mul, hite, mul_ite, ite_mul,
    mul_zero, zero_mul]
  simp only [hdU, hdV, hsU, hsV, hsd]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs <;> simp_all <;> ring
