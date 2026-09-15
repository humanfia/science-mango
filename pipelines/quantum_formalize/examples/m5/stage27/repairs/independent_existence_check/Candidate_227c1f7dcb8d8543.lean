import FrozenTarget_227c1f7dcb8d8543
theorem M5.OrderCount.C_positive_iff_realization : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  rw [M5.OrderCount.exact_C N w F hN hw hF hFN]
  simp only [Int.natCast_pos, Finset.card_pos]
  have hmem (s : ℕ) : s ∈ M5.OrderCount.positivePositions N ↔ s ∈ Finset.range N ∧ 0 < s := by
    simp [M5.OrderCount.positivePositions, and_comm]
  have hanchor (U : Finset ℕ) (hU : U ⊆ M5.OrderCount.positivePositions N)
      (hc : U.card = w - 1) :
      insert 0 U ⊆ Finset.range N ∧ 0 ∈ insert 0 U ∧ (insert 0 U).card = w := by
    have hz : 0 ∉ U := by
      intro hz
      have := (hmem 0).mp (hU hz)
      omega
    refine ⟨?_, Finset.mem_insert_self 0 U, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Finset.mem_range.mpr hN
      · exact ((hmem s).mp (hU hs)).1
    · rw [Finset.card_insert_of_notMem hz, hc]
      omega
  have herase (A : Finset ℕ) (hA : A ⊆ Finset.range N)
      (hA0 : 0 ∈ A) (hc : A.card = w) :
      A.erase 0 ∈ (M5.OrderCount.positivePositions N).powersetCard (w - 1) := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro s hs
      obtain ⟨hs0, hsA⟩ := Finset.mem_erase.mp hs
      apply (hmem s).mpr
      exact ⟨hA hsA, Nat.pos_of_ne_zero hs0⟩
    · rw [Finset.card_erase_of_mem hA0, hc]
  constructor
  · rintro ⟨⟨U, V⟩, hUV⟩
    simp only [M5.OrderCount.validPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_powersetCard] at hUV
    rcases hUV with ⟨⟨⟨hU, hUc⟩, ⟨hV, hVc⟩⟩, hgood⟩
    obtain ⟨hUA, hU0, hUw⟩ := hanchor U hU hUc
    obtain ⟨hVA, hV0, hVw⟩ := hanchor V hV hVc
    exact ⟨insert 0 U, insert 0 V, hUA, hVA, hU0, hV0, hUw, hVw, hgood⟩
  · rintro ⟨A, B, hA, hB, hA0, hB0, hAw, hBw, hconn, hsig⟩
    refine ⟨(A.erase 0, B.erase 0), ?_⟩
    have hEA := herase A hA hA0 hAw
    have hEB := herase B hB hB0 hBw
    simpa [M5.OrderCount.validPairs, Finset.insert_erase hA0,
      Finset.insert_erase hB0] using And.intro (And.intro hEA hEB) (And.intro hconn hsig)
