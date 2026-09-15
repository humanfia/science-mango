import FrozenTarget_a29f793cacb8b1b8
theorem M5.PhysicalRecovery.initial_oracle : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F
  intro N w F hN hw hF hFN
  classical
  have hs (offset : ℕ) : M5.PhysicalRecovery.selected N offset [] = {0} := by
    simp [M5.PhysicalRecovery.selected]
  have ha (offset : ℕ) : M5.PhysicalRecovery.available N offset [] = M5.OrderCount.positivePositions N := by
    ext x
    simp [M5.PhysicalRecovery.available, M5.OrderCount.positivePositions]
    constructor
    · intro hx
      aesop (config := { terminal := false }) <;> omega
    · intro hx
      refine ⟨x - 1, ?_⟩
      constructor <;> omega
  have hp : M5.ConditionalCount.PrefixOK N w ({0} : Finset ℕ) {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) := by
    simp only [M5.ConditionalCount.PrefixOK]
    simp [M5.OrderCount.positivePositions, Finset.subset_iff,
      Finset.disjoint_left, hN, hw, Nat.succ_le_iff]
    <;> aesop (config := { terminal := false }) <;> omega
  simp only [M5.PhysicalRecovery.oracle, M5.PhysicalRecovery.selectedA,
    M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.availableA,
    M5.PhysicalRecovery.availableB, hs, ha]
  rw [M5.ConditionalCount.exact_completion_C N w F {0} {0}
    (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N)
    hN hF hFN hp, M5.OrderCount.exact_C N w F hN hw hF hFN]
  have hb : ∀ U ∈ (M5.OrderCount.positivePositions N).powersetCard (w - 1), w ≤ N := by
    intro U hU
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    have hz : 0 ∉ U := by
      intro hz
      have hz' := hsub hz
      simpa [M5.OrderCount.positivePositions] using hz'
    have hi : insert 0 U ⊆ Finset.range N := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_range.mpr hN
      · have hx' := hsub hx
        simp only [M5.OrderCount.positivePositions, Finset.mem_filter,
          Finset.mem_range] at hx'
        aesop
    have hc := Finset.card_le_card hi
    simp only [Finset.card_insert_of_notMem hz, hcard, Finset.card_range] at hc
    omega
  congr 1
  apply congrArg Finset.card
  ext ⟨U, V⟩
  simp only [M5.ConditionalCount.validCompletions, M5.OrderCount.validPairs,
    Finset.card_singleton, Finset.singleton_union]
  by_cases hUw : U ∈ (M5.OrderCount.positivePositions N).powersetCard (w - 1)
  · have hwN := hb U hUw
    simp [hUw, hwN, hw, hN]
  · simp [hUw]
