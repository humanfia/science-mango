import FrozenTarget_e40733ae893e5bf2
theorem M7.PrefixCompleted.overfull_empty : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB h
  apply Finset.ext
  intro y
  simp only [Finset.notMem_empty]
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨F, hF, hx⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB x).mp hx
    have hA := Finset.card_le_card (Finset.subset_union_left : A ⊆ A ∪ x.1)
    have hB := Finset.card_le_card (Finset.subset_union_left : B ⊆ B ∪ x.2)
    unfold M5.ConditionalCount.validCompletions at hx
    simp_all [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] <;> omega
  · intro hy
    exact hy.elim
