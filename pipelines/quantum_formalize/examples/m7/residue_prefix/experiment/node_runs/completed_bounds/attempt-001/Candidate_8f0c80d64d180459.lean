import FrozenTarget_8f0c80d64d180459
theorem M7.ResiduePrefix.completed_bounds : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E A B WA WB hBase x hx
    classical
    have hA : Disjoint A WA := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    have hB : Disjoint B WB := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    have hWithin := ((M7.PrefixCompleted.completed_membership N w E A B WA WB hA hB x).mp hx).1
    simp only [M7.PrefixCompleted.Base, M7.PrefixCompleted.Within,
      Finset.subset_iff, Finset.mem_union, Finset.mem_sdiff] at hBase hWithin ⊢
    aesop
