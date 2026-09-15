import FrozenTarget_7621c44e602c6006
theorem M5.OrderCount.exact_C : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
  intro N w F hN hw hF hFN
  classical
  by_cases hwN : w ≤ N
  · have hC : M5.OrderCount.C N w F = M5.OrderCount.rawC N w F := by
      simp [M5.OrderCount.C, hN, hw, hwN, hF, hFN]
    rw [hC, M5.OrderCount.arithmetic_indicator_expansion N w F hN hw hF hFN]
    unfold M5.OrderCount.validPairs
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    unfold M5.OrderCount.pairIndicator
    rw [M5.Connectivity.connected_indicator N _ _ hN,
      M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN]
    split_ifs <;> simp_all
  · have hempty : (M5.OrderCount.positivePositions N).powersetCard (w - 1) = ∅ := by
      ext U
      constructor
      · intro hU
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
        have hzero : 0 ∉ U := by
          intro hz
          have := hsub hz
          simpa [M5.OrderCount.positivePositions] using this
        have hins : insert 0 U ⊆ Finset.range N := by
          intro s hs
          rcases Finset.mem_insert.mp hs with hs | hs
          · subst s
            exact Finset.mem_range.mpr hN
          · have hp := hsub hs
            exact (Finset.mem_filter.mp hp).1
        have hle := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hzero, Finset.card_range, hcard] at hle
        have : False := by omega
        exact this.elim
      · simp
    simp [M5.OrderCount.C, hwN, M5.OrderCount.validPairs, hempty]
