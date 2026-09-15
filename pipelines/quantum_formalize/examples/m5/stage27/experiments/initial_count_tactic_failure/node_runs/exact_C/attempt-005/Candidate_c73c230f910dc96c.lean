import FrozenTarget_c73c230f910dc96c
theorem M5.OrderCount.exact_C : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
  intro N w F hN hw hF hFN
  classical
  by_cases hwN : w ≤ N
  · have hC : M5.OrderCount.C N w F = M5.OrderCount.rawC N w F := by
      simp [M5.OrderCount.C, hN, hw, hwN, Nat.not_lt.mpr hwN]
    rw [hC, M5.OrderCount.arithmetic_indicator_expansion N w F hN hw hF hFN]
    unfold M5.OrderCount.validPairs
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      Finset.sum_filter, Finset.sum_product']
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    unfold M5.OrderCount.pairIndicator
    rw [M5.Connectivity.connected_indicator N _ _ hN,
      M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
      have hzero : 0 ∉ M5.OrderCount.positivePositions N := by
        simp [M5.OrderCount.positivePositions]
      have hzeroU : 0 ∉ U := fun hz => hzero (hsub hz)
      have hbound : insert 0 U ⊆ Finset.range N := by
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact Finset.mem_range.mpr hN
        · have hs' := hsub hs
          simp [M5.OrderCount.positivePositions] at hs'
          apply Finset.mem_range.mpr
          omega
      have hc := Finset.card_le_card hbound
      rw [Finset.card_insert_of_notMem hzeroU, Finset.card_range, hcard] at hc
      omega
    simp [M5.OrderCount.C, M5.OrderCount.validPairs, hempty, hN, hw, hwN,
      show N < w by omega]
