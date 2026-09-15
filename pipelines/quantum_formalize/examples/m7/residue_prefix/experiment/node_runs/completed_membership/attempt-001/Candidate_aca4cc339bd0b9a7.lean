import FrozenTarget_aca4cc339bd0b9a7
theorem M7.ResiduePrefix.completed_membership : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E A B WA WB hBase x
    classical
    have hDA : Disjoint A WA := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    have hDB : Disjoint B WB := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    change x ∈ (M7.PrefixCompleted.completed N w E A B WA WB).image
        (M7.ResiduePrefix.decodePair N) ↔ _
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, heq⟩
      have hb := M7.ResiduePrefix.completed_bounds N w E A B WA WB hBase y hy
      have hr : M7.ResiduePrefix.encodePair (M7.ResiduePrefix.decodePair N y) = y := by
        apply Prod.ext
        · exact M7.ResiduePrefix.nat_roundtrip N y.1 hb.1
        · exact M7.ResiduePrefix.nat_roundtrip N y.2 hb.2
      have he : M7.ResiduePrefix.encodePair x = y := by
        rw [← heq]
        exact hr
      rw [he]
      exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB y).mp hy
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨M7.ResiduePrefix.encodePair x, ?_, ?_⟩
      · exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB
          (M7.ResiduePrefix.encodePair x)).mpr hx
      · apply Prod.ext
        · exact M7.ResiduePrefix.residue_roundtrip N x.1
        · exact M7.ResiduePrefix.residue_roundtrip N x.2
