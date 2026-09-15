import FrozenTarget_e891e161ec59b1e8
theorem M7.ResiduePrefix.completed_membership : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x : Finset (ZMod N) × Finset (ZMod N), x ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB (M7.ResiduePrefix.encodePair x) ∧ M7.PrefixCompleted.Valid N w E (M7.ResiduePrefix.encodePair x)
  intro N inst w E A B WA WB hBase x
  classical
  have hDA : Disjoint A WA := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hDB : Disjoint B WB := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  unfold M7.ResiduePrefix.completed
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hb := M7.ResiduePrefix.completed_bounds N w E A B WA WB hBase y hy
    have hr : M7.ResiduePrefix.encodePair (M7.ResiduePrefix.decodePair N y) = y := by
      apply Prod.ext
      · exact M7.ResiduePrefix.nat_roundtrip N y.1 hb.1
      · exact M7.ResiduePrefix.nat_roundtrip N y.2 hb.2
    rw [← hxy, hr]
    exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB y).mp hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨M7.ResiduePrefix.encodePair x, ?_, ?_⟩
    · exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB (M7.ResiduePrefix.encodePair x)).mpr hx
    · apply Prod.ext
      · exact M7.ResiduePrefix.residue_roundtrip N x.1
      · exact M7.ResiduePrefix.residue_roundtrip N x.2
