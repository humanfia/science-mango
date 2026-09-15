import FrozenTarget_884510f32a27cb8e
theorem M5.OrderCount.C_positive_iff_realization : QuantumHarnessFrozenTarget := by
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
