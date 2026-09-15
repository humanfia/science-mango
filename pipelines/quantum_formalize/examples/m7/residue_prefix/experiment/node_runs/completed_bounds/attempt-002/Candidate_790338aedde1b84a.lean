import FrozenTarget_790338aedde1b84a
theorem M7.ResiduePrefix.completed_bounds : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hBase x hx
  classical
  have hDA : Disjoint A WA := by
    unfold M7.PrefixCompleted.Base at hBase
    aesop
  have hDB : Disjoint B WB := by
    unfold M7.PrefixCompleted.Base at hBase
    aesop
  have hWithin := ((M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x).mp hx).1
  unfold M7.PrefixCompleted.Base at hBase
  unfold M7.PrefixCompleted.Within at hWithin
  simp only [Finset.subset_iff, Finset.mem_union] at hBase hWithin ⊢
  aesop
