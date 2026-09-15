import FrozenTarget_096b73c59b8975ed
theorem M7.PrefixCompleted.left_sets : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hDE : Disjoint A (WA.erase i) := hDA.mono_right (Finset.erase_subset i WA)
  have hDI : Disjoint (insert i A) (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Finset.mem_erase.mp hk).1 rfl
    · exact Finset.disjoint_left.mp hDA hj (Finset.mem_erase.mp hk).2
  have hUnion : insert i A ∪ WA.erase i = A ∪ WA := by
    ext j
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    by_cases h : j = i <;> simp_all
  apply Finset.ext
  intro x
  rw [Finset.mem_union,
    M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x,
    M7.PrefixCompleted.completed_membership N w E A B (WA.erase i) WB hDE hDB x,
    M7.PrefixCompleted.completed_membership N w E (insert i A) B (WA.erase i) WB hDI hDB x]
  unfold M7.PrefixCompleted.Within
  constructor
  · rintro ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩
    by_cases hx : i ∈ x.1
    · right
      refine ⟨⟨?_, ?_, hBX, hXB⟩, hv⟩
      · exact Finset.insert_subset_iff.mpr ⟨hx, hAX⟩
      · simpa only [hUnion] using hXA
    · left
      refine ⟨⟨hAX, ?_, hBX, hXB⟩, hv⟩
      intro j hj
      rcases Finset.mem_union.mp (hXA hj) with ha | hw
      · exact Finset.mem_union.mpr (Or.inl ha)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_erase.mpr
        refine ⟨?_, hw⟩
        intro hji
        subst j
        exact hx hj
  · rintro (⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩ | ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩)
    · refine ⟨⟨hAX, ?_, hBX, hXB⟩, hv⟩
      exact hXA.trans (Finset.union_subset_union (by rfl) (Finset.erase_subset i WA))
    · refine ⟨⟨?_, ?_, hBX, hXB⟩, hv⟩
      · intro j hj
        exact hAX (Finset.mem_insert.mpr (Or.inr hj))
      · simpa only [hUnion] using hXA
