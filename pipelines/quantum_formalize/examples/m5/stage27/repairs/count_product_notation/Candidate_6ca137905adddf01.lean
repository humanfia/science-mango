import FrozenTarget_6ca137905adddf01
theorem M5.OrderCount.exact_C : QuantumHarnessFrozenTarget := by
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
    rw [M5.Connectivity.connected_indicator N (insert 0 U) (insert 0 V) hN]
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
