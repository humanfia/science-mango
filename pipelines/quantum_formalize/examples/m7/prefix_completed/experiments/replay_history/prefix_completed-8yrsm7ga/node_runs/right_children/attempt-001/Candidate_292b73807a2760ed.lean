import FrozenTarget_292b73807a2760ed
theorem M7.PrefixCompleted.right_children : QuantumHarnessFrozenTarget := by
  intro N w E A B WA WB i hi h
  unfold M7.PrefixCompleted.Base at h ⊢
  rcases h with ⟨hA0, hB0, hA, hB, hWA, hWB, hDA, hDB⟩
  have hWB' : WB.erase i ⊆ Finset.range N := by
    intro x hx
    exact hWB (Finset.mem_erase.mp hx).2
  have hDB' : Disjoint B (WB.erase i) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp hDB hx (Finset.mem_erase.mp hy).2
  constructor
  · exact ⟨hA0, hB0, hA, hB, hWA, hWB', hDA, hDB'⟩
  · refine ⟨hA0, Finset.mem_insert_of_mem hB0, hA, ?_, hWA, hWB', hDA, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst x
        exact hWB hi
      · exact hB hx
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst x
        exact (Finset.mem_erase.mp hy).1 rfl
      · exact Finset.disjoint_left.mp hDB' hx hy
