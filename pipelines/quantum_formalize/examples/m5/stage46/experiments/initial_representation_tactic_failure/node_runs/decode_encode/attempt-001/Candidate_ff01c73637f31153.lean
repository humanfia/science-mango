import FrozenTarget_ff01c73637f31153
theorem M5.PhysicalRecovery.decode_encode : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → A ⊆ Finset.range N → B ⊆ Finset.range N → 0 ∈ A → 0 ∈ B → _
  intro N A B hN hA hB hA0 hB0
  have decode : ∀ (offset : ℕ) (p : List Bool) (S : Finset ℕ),
      S ⊆ Finset.range N → 0 ∈ S →
      (∀ i, i < N - 1 → (p[offset + i]? = some true ↔ i + 1 ∈ S)) →
      M5.PhysicalRecovery.selected N offset p = S := by
    intro offset p S hS hS0 hp
    ext s
    simp only [M5.PhysicalRecovery.selected, Finset.mem_insert,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (rfl | ⟨i, ⟨hi, hpi⟩, rfl⟩)
      · exact hS0
      · exact (hp i hi).mp hpi
    · intro hs
      by_cases hs0 : s = 0
      · exact Or.inl hs0
      · right
        have hsN : s < N := Finset.mem_range.mp (hS hs)
        have hi : s - 1 < N - 1 := by omega
        have he : s - 1 + 1 = s := by omega
        refine ⟨s - 1, ⟨hi, ?_⟩, he⟩
        apply (hp (s - 1) hi).mpr
        simpa only [he] using hs
  constructor
  · unfold M5.PhysicalRecovery.selectedA
    apply decode _ _ A hA hA0
    intro i hi
    have hit : i < M5.PhysicalRecovery.decisionCount N := by
      unfold M5.PhysicalRecovery.decisionCount
      omega
    simp [M5.PhysicalRecovery.encode, List.getElem?_ofFn, hi, hit]
  · unfold M5.PhysicalRecovery.selectedB
    apply decode _ _ B hB hB0
    intro i hi
    have hit : N - 1 + i < M5.PhysicalRecovery.decisionCount N := by
      unfold M5.PhysicalRecovery.decisionCount
      omega
    have hnot : ¬ N - 1 + i < N - 1 := by omega
    simp [M5.PhysicalRecovery.encode, List.getElem?_ofFn, hit, hnot]
