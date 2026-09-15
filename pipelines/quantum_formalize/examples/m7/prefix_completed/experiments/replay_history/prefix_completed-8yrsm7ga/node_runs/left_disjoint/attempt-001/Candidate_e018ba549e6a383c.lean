import FrozenTarget_e018ba549e6a383c
theorem M7.PrefixCompleted.left_disjoint : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hD0 : Disjoint A (WA.erase i) :=
    hDA.mono_right (Finset.erase_subset i WA)
  have hD1 : Disjoint (insert i A) (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Finset.mem_erase.mp hk).1 rfl
    · exact Finset.disjoint_left.mp hDA hj (Finset.mem_erase.mp hk).2
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩ :=
    (M7.PrefixCompleted.completed_membership N w E A B (WA.erase i) WB hD0 hDB x).mp hx
  obtain ⟨⟨hIX, hXI, hBX', hXB'⟩, hv'⟩ :=
    (M7.PrefixCompleted.completed_membership N w E (insert i A) B (WA.erase i) WB hD1 hDB x).mp hy
  have hiX : i ∈ x.1 := hIX (Finset.mem_insert_self i A)
  rcases Finset.mem_union.mp (hXA hiX) with hiA | hiW
  · exact Finset.disjoint_left.mp hDA hiA hi
  · exact (Finset.mem_erase.mp hiW).1 rfl
