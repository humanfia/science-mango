import FrozenTarget_f8d97b2faadecf1d
theorem M7.ResiduePrefix.completed_bounds : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hBase x hx
  have hDA : Disjoint A WA := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hDB : Disjoint B WB := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWithin := ((M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x).mp hx).1
  have hXA : x.1 ⊆ A ∪ WA := by
    unfold M7.PrefixCompleted.Within at hWithin
    tauto
  have hXB : x.2 ⊆ B ∪ WB := by
    unfold M7.PrefixCompleted.Within at hWithin
    tauto
  have hA : A ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hB : B ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWA : WA ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWB : WB ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  constructor
  · intro i hi
    rcases Finset.mem_union.mp (hXA hi) with h | h
    · exact hA h
    · exact hWA h
  · intro i hi
    rcases Finset.mem_union.mp (hXB hi) with h | h
    · exact hB h
    · exact hWB h
