import FrozenTarget_fbd2b9d232a7974e
theorem M7.OrbitResidual.subtraction_partition : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst C0 C1 bases hsep hdisj
  have hd : Disjoint (M7.OrbitResidual.remaining C0 bases)
      (M7.OrbitResidual.remaining C1 bases) := by
    unfold M7.OrbitResidual.remaining
    exact hdisj.mono Finset.sdiff_subset Finset.sdiff_subset
  rw [M7.OrbitResidual.subtraction_card N (C0 ∪ C1) bases hsep,
      M7.OrbitResidual.subtraction_card N C0 bases hsep,
      M7.OrbitResidual.subtraction_card N C1 bases hsep,
      M7.OrbitResidual.remaining_partition N C0 C1 bases,
      Finset.card_union_of_disjoint hd, Nat.cast_add]
