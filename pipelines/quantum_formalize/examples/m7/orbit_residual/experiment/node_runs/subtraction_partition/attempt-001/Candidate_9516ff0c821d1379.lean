import FrozenTarget_9516ff0c821d1379
theorem M7.OrbitResidual.subtraction_partition : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst C0 C1 bases hsep hdisj
    have hremaining : Disjoint (M7.OrbitResidual.remaining C0 bases)
        (M7.OrbitResidual.remaining C1 bases) := by
      unfold M7.OrbitResidual.remaining
      exact hdisj.mono Finset.sdiff_subset Finset.sdiff_subset
    rw [M7.OrbitResidual.subtraction_card N (C0 ∪ C1) bases hsep,
      M7.OrbitResidual.subtraction_card N C0 bases hsep,
      M7.OrbitResidual.subtraction_card N C1 bases hsep,
      M7.OrbitResidual.remaining_partition N C0 C1 bases,
      Finset.card_union_of_disjoint hremaining,
      Nat.cast_add]
