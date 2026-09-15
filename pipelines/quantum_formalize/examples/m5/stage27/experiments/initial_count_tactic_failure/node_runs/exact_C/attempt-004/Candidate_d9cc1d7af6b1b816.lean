import FrozenTarget_d9cc1d7af6b1b816
theorem M5.OrderCount.exact_C : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
  intro N w F hN hw hF hFN
  classical
  by_cases hwN : w ≤ N
  · have hC : M5.OrderCount.C N w F = M5.OrderCount.rawC N w F := by
      simp [M5.OrderCount.C, hwN, hFN]
    rw [hC, M5.OrderCount.arithmetic_indicator_expansion N w F hN hw hF hFN]
    unfold M5.OrderCount.validPairs
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    simp only [Finset.sum_product']
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    unfold M5.OrderCount.pairIndicator
    rw [M5.Connectivity.connected_indicator N (insert 0 U) (insert 0 V) hN,
      M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hsub : M5.OrderCount.positivePositions N ⊆ (Finset.range N).erase 0 := by
      intro s hs
      simp [M5.OrderCount.positivePositions] at hs
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    have hcard : ((Finset.range N).erase 0).card = N - 1 := by
      rw [Finset.card_erase_of_mem (by simpa using hN), Finset.card_range]
    have hsmall : (M5.OrderCount.positivePositions N).card < w - 1 := by
      have hle := Finset.card_le_card hsub
      rw [hcard] at hle
      omega
    have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      obtain ⟨hsubU, hcardU⟩ := Finset.mem_powersetCard.mp hU
      have hle := Finset.card_le_card hsubU
      omega
    simp [M5.OrderCount.C, hwN, M5.OrderCount.validPairs, hempty]
