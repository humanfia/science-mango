import FrozenTarget_ca9d5e99a283d353
theorem M7.PrefixCompleted.overfull_empty : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N w E A B WA WB h
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    change x ∈ (M7.PrefixSector.completions N w E A B WA WB).image (fun y => (A ∪ y.1, B ∪ y.2)) at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases (M7.PrefixSector.completion_membership N w E A B WA WB y).mp hy with ⟨F, hF, hy⟩
    simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powersetCard] at hy
    have ha : A.card ≤ (A ∪ y.1).card := Finset.card_le_card Finset.subset_union_left
    have hb : B.card ≤ (B ∪ y.2).card := Finset.card_le_card Finset.subset_union_left
    have hca : (A ∪ y.1).card = w := hy.2.1
    have hcb : (B ∪ y.2).card = w := hy.2.2.1
    omega
