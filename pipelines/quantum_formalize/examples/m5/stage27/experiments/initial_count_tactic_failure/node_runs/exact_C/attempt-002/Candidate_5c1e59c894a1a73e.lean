import FrozenTarget_5c1e59c894a1a73e
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
    rw [← Finset.sum_product]
    apply Finset.sum_congr rfl
    rintro ⟨U, V⟩ hUV
    unfold M5.OrderCount.pairIndicator
    rw [M5.Connectivity.connected_indicator N (insert 0 U) (insert 0 V) hN]
    rw [M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hc : (M5.OrderCount.positivePositions N).card = N - 1 := by
      simp [M5.OrderCount.positivePositions, hN]
    have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      apply Finset.ext
      intro U
      simp only [Finset.not_mem_empty, iff_false]
      intro hU
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
      have hle := Finset.card_le_card hsub
      rw [hc, hcard] at hle
      omega
    simp [M5.OrderCount.C, M5.OrderCount.validPairs, hempty, hwN, hFN]
