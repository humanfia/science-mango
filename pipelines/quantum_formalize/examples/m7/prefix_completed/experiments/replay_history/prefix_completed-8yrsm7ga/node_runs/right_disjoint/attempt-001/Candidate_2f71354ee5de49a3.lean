import FrozenTarget_2f71354ee5de49a3
theorem M7.PrefixCompleted.right_disjoint : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hDB' : Disjoint B (WB.erase i) :=
    hDB.mono_right (Finset.erase_subset i WB)
  have hDI : Disjoint (insert i B) (WB.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_insert.mp hj with hji | hjB
    · subst j
      simp at hk
    · exact Finset.disjoint_left.mp hDB hjB (Finset.mem_of_mem_erase hk)
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxW := ((M7.PrefixCompleted.completed_membership N w E A B WA (WB.erase i) hDA hDB' x).mp hx).1
  have hyW := ((M7.PrefixCompleted.completed_membership N w E A (insert i B) WA (WB.erase i) hDA hDI x).mp hy).1
  have hiX : i ∈ x.2 := hyW.2.2.1 (Finset.mem_insert_self i B)
  rcases Finset.mem_union.mp (hxW.2.2.2 hiX) with hiB | hiE
  · exact Finset.disjoint_left.mp hDB hiB hi
  · simp at hiE
