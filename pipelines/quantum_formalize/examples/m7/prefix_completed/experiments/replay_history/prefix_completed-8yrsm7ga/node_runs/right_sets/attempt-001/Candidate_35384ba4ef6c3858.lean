import FrozenTarget_35384ba4ef6c3858
theorem M7.PrefixCompleted.right_sets : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hDE : Disjoint B (WB.erase i) :=
    hDB.mono_right (Finset.erase_subset i WB)
  have hDI : Disjoint (insert i B) (WB.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hjW
    rcases Finset.mem_insert.mp hj with rfl | hjB
    · exact (Finset.mem_erase.mp hjW).1 rfl
    · exact Finset.disjoint_left.mp hDB hjB (Finset.mem_erase.mp hjW).2
  have hcap : insert i B ∪ WB.erase i = B ∪ WB := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji]
  apply Finset.ext
  intro x
  rw [Finset.mem_union,
    M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x,
    M7.PrefixCompleted.completed_membership N w E A B WA (WB.erase i) hDA hDE x,
    M7.PrefixCompleted.completed_membership N w E A (insert i B) WA (WB.erase i) hDA hDI x]
  unfold M7.PrefixCompleted.Within
  rw [hcap]
  constructor
  · rintro ⟨⟨hAX, hXA, hBX, hXB⟩, hV⟩
    by_cases hix : i ∈ x.2
    · right
      refine ⟨⟨hAX, hXA, ?_, hXB⟩, hV⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hix
      · exact hBX hj
    · left
      refine ⟨⟨hAX, hXA, hBX, ?_⟩, hV⟩
      intro j hj
      rcases Finset.mem_union.mp (hXB hj) with hjB | hjW
      · exact Finset.mem_union.mpr (Or.inl hjB)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_erase.mpr
        refine ⟨?_, hjW⟩
        intro hji
        subst j
        exact hix hj
  · rintro (⟨⟨hAX, hXA, hBX, hXB⟩, hV⟩ | ⟨⟨hAX, hXA, hBX, hXB⟩, hV⟩)
    · refine ⟨⟨hAX, hXA, hBX, ?_⟩, hV⟩
      intro j hj
      rcases Finset.mem_union.mp (hXB hj) with hjB | hjW
      · exact Finset.mem_union.mpr (Or.inl hjB)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mp hjW).2)
    · refine ⟨⟨hAX, hXA, ?_, hXB⟩, hV⟩
      intro j hj
      exact hBX (Finset.mem_insert_of_mem hj)
