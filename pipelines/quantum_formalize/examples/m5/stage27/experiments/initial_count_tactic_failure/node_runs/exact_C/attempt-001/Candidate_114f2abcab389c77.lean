import FrozenTarget_114f2abcab389c77
theorem M5.OrderCount.exact_C : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
  intro N w F hN hw hF hFN
  classical
  by_cases hwN : w ≤ N
  · have hC : M5.OrderCount.C N w F = M5.OrderCount.rawC N w F := by
      simp [M5.OrderCount.C, hN, hw, hF, hFN, hwN, Nat.ne_of_gt hN, Nat.ne_of_gt hw, not_lt.mpr hwN]
    rw [hC, M5.OrderCount.arithmetic_indicator_expansion N w F hN hw hF hFN]
    simp only [M5.OrderCount.validPairs, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    unfold M5.OrderCount.pairIndicator
    rw [M5.Connectivity.connected_indicator _ _ _ hN,
      M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hpositions : M5.OrderCount.positivePositions N = (Finset.range N).erase 0 := by
      ext s
      simp [M5.OrderCount.positivePositions]
      <;> omega
    have hcard : (M5.OrderCount.positivePositions N).card = N - 1 := by
      rw [hpositions]
      simp [Finset.card_erase_of_mem, Finset.mem_range.mpr hN]
    have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro U hU
      obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hU
      have hle := Finset.card_le_card hsub
      omega
    simp [M5.OrderCount.C, M5.OrderCount.validPairs, hempty, hwN,
      hN, hw, hF, hFN, Nat.ne_of_gt hN, Nat.ne_of_gt hw, Nat.lt_of_not_ge hwN]
