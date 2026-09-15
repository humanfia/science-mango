import FrozenTarget_d055de38f2df8368
theorem M7.PrefixCompleted.left_children : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB i hi h
  unfold M7.PrefixCompleted.Base at h ⊢
  rcases h with ⟨hA0, hB0, hA, hB, hWA, hWB, hDA, hDB⟩
  have hErase : WA.erase i ⊆ Finset.range N := by
    intro a ha
    exact hWA (Finset.mem_of_mem_erase ha)
  have hDisj : Disjoint A (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro a ha hw
    exact Finset.disjoint_left.mp hDA ha (Finset.mem_of_mem_erase hw)
  constructor
  · exact ⟨hA0, hB0, hA, hB, hErase, hWB, hDisj, hDB⟩
  · refine ⟨Finset.mem_insert_of_mem hA0, hB0, ?_, hB, hErase, hWB, ?_, hDB⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hWA hi
      · exact hA ha
    · apply Finset.disjoint_left.mpr
      intro a ha hw
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (Finset.mem_erase.mp hw).1 rfl
      · exact Finset.disjoint_left.mp hDisj ha hw
