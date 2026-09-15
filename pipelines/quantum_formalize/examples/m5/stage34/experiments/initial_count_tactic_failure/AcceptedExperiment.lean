import M5ConditionalCount

theorem M5.ConditionalCount.restricted_subset_domain : ∀ (W : Finset ℕ) (d k : ℕ), (M5.ConditionalCount.restricted W d).powersetCard k = (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s) := by
  intro W d k
  classical
  change (W.filter (fun s => d ∣ s)).powersetCard k =
    (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  apply Finset.ext
  intro U
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hk⟩
    refine ⟨⟨?_, hk⟩, ?_⟩
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).1
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).2
  · rintro ⟨⟨hU, hk⟩, hd⟩
    refine ⟨?_, hk⟩
    intro s hs
    exact Finset.mem_filter.mpr ⟨hU hs, hd s hs⟩

theorem M5.ConditionalCount.selected_divisor_indicator : ∀ (N : ℕ) (A B U V : Finset ℕ), 0 < N → M5.ConditionalCount.selectedDivisorSum N A B U V = (if M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 then (1 : ℤ) else 0) := by
  intro N A B U V hN
  classical
  have hgN : M5.Connectivity.supportGcd N A B ∣ N :=
    ((M5.Connectivity.support_gcd_dvd N (M5.Connectivity.supportGcd N A B) A B).mp (dvd_refl _)).1
  have hgpos : 0 < M5.Connectivity.supportGcd N A B := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : N = 0 := by simpa [hz] using hgN
    omega
  have hd : ∀ d : ℕ,
      d ∣ M5.Connectivity.supportGcd (M5.Connectivity.supportGcd N A B) U V ↔
      d ∣ M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) := by
    intro d
    simp only [M5.Connectivity.support_gcd_dvd, Finset.mem_union, or_imp, forall_and]
    tauto
  have heq : M5.Connectivity.supportGcd (M5.Connectivity.supportGcd N A B) U V =
      M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) := by
    apply Nat.dvd_antisymm
    · exact (hd _).mp (dvd_refl _)
    · exact (hd _).mpr (dvd_refl _)
  simpa only [M5.ConditionalCount.selectedDivisorSum, heq] using
    (M5.Connectivity.connected_indicator (M5.Connectivity.supportGcd N A B) U V hgpos)

theorem M5.ConditionalCount.two_block_completion_count : ∀ (P : M5.BinaryPolynomial) (A B WA WB : Finset ℕ) (kA kB : ℕ), P.Monic → Disjoint A WA → Disjoint B WB → M5.ConditionalCount.nSelected P A WA kA * M5.ConditionalCount.nSelected P B WB kB = M5.ConditionalCount.twoBlockIndicatorSum P A B WA WB kA kB := by
  classical
  intro P A B WA WB kA kB hP hA hB
  simp only [M5.ConditionalCount.nSelected, dif_pos hP]
  rw [M5.CompletionBlock.completion_count P hP A WA kA hA,
    M5.CompletionBlock.completion_count P hP B WB kB hB]
  unfold M5.CompletionBlock.count M5.ConditionalCount.twoBlockIndicatorSum
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hUA : P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) <;>
    by_cases hVB : P ∣ M5.SupportPolynomial.ofSupport (B ∪ V) <;>
    simp [hUA, hVB]

theorem M5.ConditionalCount.conditional_arithmetic_expansion : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.ConditionalCount.PrefixOK N w A B WA WB → M5.ConditionalCount.rawCompletion N w F A B WA WB = ∑ U ∈ WA.powersetCard (w-A.card), ∑ V ∈ WB.powersetCard (w-B.card), M5.ConditionalCount.pairIndicator N F A B U V := by
  classical
  intro N w F A B WA WB hN hF hFN hprefix
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hprefix
    tauto
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hprefix
    tauto
  have hAr (d : ℕ) : Disjoint A (M5.ConditionalCount.restricted WA d) := by
    exact hA.mono_right (Finset.filter_subset _ _)
  have hBr (d : ℕ) : Disjoint B (M5.ConditionalCount.restricted WB d) := by
    exact hB.mono_right (Finset.filter_subset _ _)
  have hprod (H : Finset M5.BinaryPolynomial)
      (hH : ∀ p ∈ H, p.Monic) : (∏ p ∈ H, p).Monic := by
    induction H using Finset.induction_on with
    | empty => simp
    | @insert p H hp ih =>
        rw [Finset.prod_insert hp]
        exact (hH p (Finset.mem_insert_self p H)).mul
          (ih (fun q hq => hH q (Finset.mem_insert_of_mem hq)))
  have hblock (d : ℕ) (H : Finset M5.BinaryPolynomial)
      (hH : H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) A
          (M5.ConditionalCount.restricted WA d) (w - A.card) *
        M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) B
          (M5.ConditionalCount.restricted WB d) (w - B.card) =
        M5.ConditionalCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p) A B
          (M5.ConditionalCount.restricted WA d)
          (M5.ConditionalCount.restricted WB d) (w - A.card) (w - B.card) := by
    apply M5.ConditionalCount.two_block_completion_count
    · apply hF.mul
      apply hprod
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        ((Finset.mem_powerset.mp hH) hp)).1
    · exact hAr d
    · exact hBr d
  unfold M5.ConditionalCount.rawCompletion
  simp only [mul_assoc]
  simp (disch := assumption) only [hblock]
  unfold M5.ConditionalCount.twoBlockIndicatorSum M5.ConditionalCount.pairIndicator M5.PolynomialIndicator.factorExclusionSum
  simp only [M5.ConditionalCount.restricted_subset_domain, Finset.sum_filter]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.ite_sum_zero, ite_mul, mul_ite, mul_zero, zero_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext S
    rw [Finset.sum_comm]
    arg 2
    ext U
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext U
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_one]
  split_ifs <;> simp_all
#print axioms M5.ConditionalCount.restricted_subset_domain
#print axioms M5.ConditionalCount.selected_divisor_indicator
#print axioms M5.ConditionalCount.two_block_completion_count
#print axioms M5.ConditionalCount.conditional_arithmetic_expansion
