import FrozenTarget_8ffdf9bc01a48f00
theorem M7.PrefixCompleted.overfull_empty : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB h
  change (M7.PrefixSector.completions N w E A B WA WB).image (fun x => (A ∪ x.1, B ∪ x.2)) = ∅
  have hempty : M7.PrefixSector.completions N w E A B WA WB = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨F, hF, hx⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB x).mp hx
    have hA : A.card ≤ (A ∪ x.1).card := Finset.card_le_card Finset.subset_union_left
    have hB : B.card ≤ (B ∪ x.2).card := Finset.card_le_card Finset.subset_union_left
    unfold M5.ConditionalCount.validCompletions at hx
    split_ifs at hx <;>
      simp_all [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] <;>
      omega
  rw [hempty]
  simp
