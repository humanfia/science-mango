import M5OrderCount
import M5ConditionalCount
import M5BinaryRecovery
import M5PrefixPartition

theorem M5.OrderCount.divisor_subset_domain : ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s) := by
  change ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  intro N d k
  classical
  ext U
  simp [M5.OrderCount.divisorPositions, Finset.mem_powersetCard, Finset.subset_iff, forall_and, and_assoc, and_left_comm, and_comm]

theorem M5.OrderCount.two_block_divisibility_count : ∀ (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ), P.Monic → 0 ∉ W → M5.OrderCount.nOne P W k ^ 2 = M5.OrderCount.twoBlockIndicatorSum P W k := by
  classical
  intro P W k hP hW
  simp only [M5.OrderCount.nOne, dif_pos hP]
  rw [M5.AnchoredCount.anchored_single_block_count P hP W k hW]
  unfold M5.AnchoredCount.count M5.OrderCount.twoBlockIndicatorSum
  simp only [pow_two, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, ite_and]
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

theorem M5.OrderCount.arithmetic_indicator_expansion : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.rawC N w F = ∑ U ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), ∑ V ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), M5.OrderCount.pairIndicator N F U V := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  have hprod : ∀ S : Finset M5.BinaryPolynomial, (∀ p ∈ S, p.Monic) → (∏ p ∈ S, p).Monic := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro h
        simpa using (Polynomial.monic_one : (1 : M5.BinaryPolynomial).Monic)
    | @insert p S hp ih =>
        intro h
        rw [Finset.prod_insert hp]
        exact (h p (Finset.mem_insert_self p S)).mul
          (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))
  have hexpand (d : ℕ) :
      (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (-1 : ℤ) ^ S.card * M5.OrderCount.nOne (F * ∏ p ∈ S, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2) =
      ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (-1 : ℤ) ^ S.card * M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ S, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) := by
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    apply M5.OrderCount.two_block_divisibility_count
    · apply hF.mul
      apply hprod
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        (Finset.mem_powerset.mp hS hp)).1
    · simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  unfold M5.OrderCount.rawC
  simp_rw [hexpand]
  unfold M5.OrderCount.twoBlockIndicatorSum M5.OrderCount.pairIndicator
  unfold M5.PolynomialIndicator.factorExclusionSum
  simp_rw [M5.OrderCount.divisor_subset_domain]
  simp only [Finset.sum_filter, Finset.forall_mem_insert, dvd_zero, true_and]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.ite_sum_zero,
    ite_mul, mul_ite, mul_zero, zero_mul]
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

theorem M5.OrderCount.exact_C : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
  intro N w F hN hw hF hFN
  classical
  by_cases hwN : w ≤ N
  · have hC : M5.OrderCount.C N w F = M5.OrderCount.rawC N w F := by
      simp [M5.OrderCount.C, hFN, hwN]
    rw [hC, M5.OrderCount.arithmetic_indicator_expansion N w F hN hw hF hFN]
    unfold M5.OrderCount.validPairs
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    unfold M5.OrderCount.pairIndicator
    have hconn : (∑ d ∈ N.divisors,
        if (∀ s ∈ insert 0 U, d ∣ s) ∧ (∀ s ∈ insert 0 V, d ∣ s)
        then ArithmeticFunction.moebius d else 0) =
        (if M5.Connectivity.supportGcd N (insert 0 U) (insert 0 V) = 1 then (1 : ℤ) else 0) := by
      convert M5.Connectivity.connected_indicator N (insert 0 U) (insert 0 V) hN using 1
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp_all
    rw [hconn]
    rw [M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hc : (M5.OrderCount.positivePositions N).card = N - 1 := by
      have heq : M5.OrderCount.positivePositions N = (Finset.range N).erase 0 := by
        ext s
        simp [M5.OrderCount.positivePositions, Nat.pos_iff_ne_zero, and_comm]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_range.mpr hN), Finset.card_range]
    have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      rw [hc]
      omega
    simp [M5.OrderCount.C, M5.OrderCount.validPairs, hempty, hwN, hFN]

theorem M5.OrderCount.C_nonnegative : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → 0 ≤ M5.OrderCount.C N w F := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → 0 ≤ M5.OrderCount.C N w F
  intro N w F hN hw hF hFN
  rw [M5.OrderCount.exact_C N w F hN hw hF hFN]
  exact Int.natCast_nonneg _

theorem M5.OrderCount.C_positive_iff_realization : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → (0 < M5.OrderCount.C N w F ↔ ∃ A B : Finset ℕ, A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧ 0 ∈ A ∧ 0 ∈ B ∧ A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F) := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  rw [M5.OrderCount.exact_C N w F hN hw hF hFN]
  have hpositions : M5.OrderCount.positivePositions N = (Finset.range N).erase 0 := by
    ext s
    simp [M5.OrderCount.positivePositions, Nat.pos_iff_ne_zero, and_comm]
  have hmem (U V : Finset ℕ) :
      (U, V) ∈ M5.OrderCount.validPairs N w F ↔
        (U ⊆ M5.OrderCount.positivePositions N ∧ U.card = w - 1) ∧
        (V ⊆ M5.OrderCount.positivePositions N ∧ V.card = w - 1) ∧
        M5.Connectivity.supportGcd N (insert 0 U) (insert 0 V) = 1 ∧
        M5.completeSignature (M5.SupportPolynomial.ofSupport (insert 0 U))
          (M5.SupportPolynomial.ofSupport (insert 0 V)) N = F := by
    simp [M5.OrderCount.validPairs, Finset.product_eq_sprod,
      Finset.mem_powersetCard, and_assoc]
  have hanchor (U : Finset ℕ)
      (hU : U ⊆ M5.OrderCount.positivePositions N) (hc : U.card = w - 1) :
      insert 0 U ⊆ Finset.range N ∧ (insert 0 U).card = w := by
    have hsub : U ⊆ (Finset.range N).erase 0 := by
      simpa only [hpositions] using hU
    have hz : 0 ∉ U := by
      intro hz
      have := hsub hz
      simp at this
    constructor
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Finset.mem_range.mpr hN
      · exact Finset.mem_of_mem_erase (hsub hs)
    · rw [Finset.card_insert_of_notMem hz, hc]
      omega
  have herase (A : Finset ℕ) (hA : A ⊆ Finset.range N)
      (hzero : 0 ∈ A) (hc : A.card = w) :
      A.erase 0 ⊆ M5.OrderCount.positivePositions N ∧ (A.erase 0).card = w - 1 := by
    constructor
    · rw [hpositions]
      intro s hs
      obtain ⟨hne, hsA⟩ := Finset.mem_erase.mp hs
      exact Finset.mem_erase.mpr ⟨hne, hA hsA⟩
    · rw [Finset.card_erase_of_mem hzero, hc]
  constructor
  · intro h
    have hc : 0 < (M5.OrderCount.validPairs N w F).card := by
      exact_mod_cast h
    obtain ⟨⟨U, V⟩, hUV⟩ := Finset.card_pos.mp hc
    obtain ⟨⟨hU, hcU⟩, ⟨hV, hcV⟩, hg, hs⟩ := (hmem U V).mp hUV
    obtain ⟨hAU, hcwU⟩ := hanchor U hU hcU
    obtain ⟨hBV, hcwV⟩ := hanchor V hV hcV
    exact ⟨insert 0 U, insert 0 V, hAU, hBV,
      Finset.mem_insert_self 0 U, Finset.mem_insert_self 0 V,
      hcwU, hcwV, hg, hs⟩
  · rintro ⟨A, B, hA, hB, hzA, hzB, hcA, hcB, hg, hs⟩
    have hU := herase A hA hzA hcA
    have hV := herase B hB hzB hcB
    have hUV : (A.erase 0, B.erase 0) ∈ M5.OrderCount.validPairs N w F := by
      apply (hmem (A.erase 0) (B.erase 0)).mpr
      refine ⟨hU, hV, ?_, ?_⟩
      · simpa only [Finset.insert_erase hzA, Finset.insert_erase hzB] using hg
      · simpa only [Finset.insert_erase hzA, Finset.insert_erase hzB] using hs
    have hc : 0 < (M5.OrderCount.validPairs N w F).card :=
      Finset.card_pos.mpr ⟨(A.erase 0, B.erase 0), hUV⟩
    exact_mod_cast hc

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

theorem M5.ConditionalCount.exact_completion_C : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.ConditionalCount.PrefixOK N w A B WA WB → M5.ConditionalCount.completionC N w F A B WA WB = (M5.ConditionalCount.validCompletions N w F A B WA WB).card := by
  classical
  intro N w F A B WA WB hN hF hFN hprefix
  have hp := hprefix
  unfold M5.ConditionalCount.PrefixOK at hp
  have hAw : A.card ≤ w := by tauto
  have hBw : B.card ≤ w := by tauto
  have hA : Disjoint A WA := by tauto
  have hB : Disjoint B WB := by tauto
  have hc : M5.ConditionalCount.completionC N w F A B WA WB =
      M5.ConditionalCount.rawCompletion N w F A B WA WB := by
    simp [M5.ConditionalCount.completionC, hAw, hBw,
      not_lt_of_ge hAw, not_lt_of_ge hBw]
  rw [hc, M5.ConditionalCount.conditional_arithmetic_expansion N w F A B WA WB hN hF hFN hprefix]
  unfold M5.ConditionalCount.validCompletions
  rw [Finset.card_filter]
  simp only [Nat.cast_sum]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hU' := Finset.mem_powersetCard.mp hU
  have hV' := Finset.mem_powersetCard.mp hV
  have hAU : (A ∪ U).card = w := by
    rw [Finset.card_union_of_disjoint (hA.mono_right hU'.1), hU'.2]
    exact Nat.add_sub_of_le hAw
  have hBV : (B ∪ V).card = w := by
    rw [Finset.card_union_of_disjoint (hB.mono_right hV'.1), hV'.2]
    exact Nat.add_sub_of_le hBw
  change M5.ConditionalCount.selectedDivisorSum N A B U V *
    M5.PolynomialIndicator.factorExclusionSum
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N = _
  rw [M5.ConditionalCount.selected_divisor_indicator N A B U V hN,
    M5.PolynomialIndicator.exact_signature_indicator
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N hN hF hFN]
  by_cases hg : M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 <;>
    by_cases hs : M5.completeSignature
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) N = F <;>
    simp [hAU, hBV, hg, hs]

theorem M5.ConditionalCount.completion_nonnegative_and_exists : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.ConditionalCount.PrefixOK N w A B WA WB → (0 ≤ M5.ConditionalCount.completionC N w F A B WA WB ∧ (0 < M5.ConditionalCount.completionC N w F A B WA WB ↔ (M5.ConditionalCount.validCompletions N w F A B WA WB).Nonempty)) := by
  intro N w F A B WA WB hN hF hFN hprefix
  rw [M5.ConditionalCount.exact_completion_C N w F A B WA WB hN hF hFN hprefix]
  constructor
  · positivity
  · exact_mod_cast (Finset.card_pos :
      0 < (M5.ConditionalCount.validCompletions N w F A B WA WB).card ↔
        (M5.ConditionalCount.validCompletions N w F A B WA WB).Nonempty)

theorem M5.BinaryRecovery.recover_length : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n
  intro c p n
  induction n generalizing p with
  | zero => simp [M5.BinaryRecovery.recover]
  | succ n ih =>
      simp only [M5.BinaryRecovery.recover]
      split <;> simp [ih, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem M5.BinaryRecovery.recover_positive : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n) := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n)
  intro c p n
  induction n generalizing p with
  | zero =>
      intro hs hp
      simpa [M5.BinaryRecovery.recover] using hp
  | succ n ih =>
      intro hs hp
      have hsplit := hs p (by omega)
      have hchild (b : Bool) : ∀ q : List Bool, q.length < (p ++ [b]).length + n → c q = c (q ++ [false]) + c (q ++ [true]) := by
        intro q hq
        apply hs q
        simp only [List.length_append, List.length_cons, List.length_nil] at hq
        omega
      by_cases hf : 0 < c (p ++ [false])
      · simpa [M5.BinaryRecovery.recover, hf] using ih (p ++ [false]) (hchild false) hf
      · have ht : 0 < c (p ++ [true]) := by omega
        simpa [M5.BinaryRecovery.recover, hf] using ih (p ++ [true]) (hchild true) ht

theorem M5.BinaryRecovery.recover_valid : ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m) := by
  change ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m)
  intro c Valid m hs hv hp
  have hlen : (M5.BinaryRecovery.recover c [] m).length = m := by
    simpa only [List.length_nil, Nat.zero_add] using M5.BinaryRecovery.recover_length c [] m
  refine ⟨hlen, hv _ hlen ?_⟩
  apply M5.BinaryRecovery.recover_positive c [] m
  · simpa only [List.length_nil, Nat.zero_add] using hs
  · exact hp

theorem M5.PrefixPartition.count_empty : ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ) := by
  change ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
  intro α W
  classical
  simp [M5.PrefixPartition.count]

theorem M5.PrefixPartition.count_terminal : ∀ (α : Type) [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length = m → M5.PrefixPartition.count W p = (if p ∈ W then 1 else 0) := by
  intro α inst W m p hW hp
  classical
  have hcount : M5.PrefixPartition.count W p = ((W.filter (fun q => p.IsPrefix q)).card : ℤ) := by
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List α) => (s.card : ℤ))
    ext q
    simp only [Finset.mem_filter]
  have hf : W.filter (fun q => p.IsPrefix q) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · intro h
      subst q
      exact List.prefix_refl p
  rw [hcount, hf]
  by_cases h : p ∈ W
  · have hs : W.filter (fun q => q = p) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hq => hq.2
      · intro hq
        subst q
        exact ⟨h, rfl⟩
    rw [hs]
    simp [h]
  · simp [h]

theorem M5.PrefixPartition.prefix_next : ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a := by
  change ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a
  intro α p q a h
  constructor
  · rintro ⟨s, rfl⟩
    constructor
    · exact ⟨[a] ++ s, by simp [List.append_assoc]⟩
    · simp [List.get_eq_getElem, List.append_assoc, List.getElem_append]
  · rintro ⟨hp, ha⟩
    simpa only [ha] using (List.concat_get_prefix hp h)

theorem M5.PrefixPartition.count_partition : ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a]) := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  have hc : (W.filter (fun q => p.IsPrefix q)).card =
      ∑ a : α, (W.filter (fun q => (p ++ [a]).IsPrefix q)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have h : p.length < q.length := by
      rw [hW q hq]
      exact hp
    have hn : ∀ a : α, (p ++ [a]).IsPrefix q ↔
        p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a :=
      fun a => M5.PrefixPartition.prefix_next α p q a h
    simp only [hn]
    by_cases hpq : p.IsPrefix q
    · simp [hpq]
    · simp [hpq]
  have hcount : ∀ p : List α, M5.PrefixPartition.count W p = ((W.filter (fun q => p.IsPrefix q)).card : ℤ) := by
    intro p
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List α) => (s.card : ℤ))
    ext q
    simp only [Finset.mem_filter]
  simp only [hcount]
  exact_mod_cast hc
