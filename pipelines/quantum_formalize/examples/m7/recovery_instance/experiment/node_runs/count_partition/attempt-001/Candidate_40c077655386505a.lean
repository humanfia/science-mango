import FrozenTarget_40c077655386505a
theorem M7.RecoveryInstance.count_partition : QuantumHarnessFrozenTarget := by
  intro N inst w E bases hE hB p hp
  classical
  rw [(M7.RecoveryInstance.count_card N w E bases hE hB p).1,
    (M7.RecoveryInstance.count_card N w E bases hE hB (p ++ [false])).1,
    (M7.RecoveryInstance.count_card N w E bases hE hB (p ++ [true])).1]
  change ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E p) bases).card : ℤ) =
    ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [false])) bases).card : ℤ) +
    ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [true])) bases).card : ℤ)
  have hpart := M7.RecoveryPrefix.completed_partition N w E p hp
  have hd : Disjoint
      (M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [false])) bases)
      (M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [true])) bases) := by
    unfold M7.OrbitResidual.remaining
    exact hpart.2.mono Finset.sdiff_subset Finset.sdiff_subset
  rw [hpart.1, M7.OrbitResidual.remaining_partition,
    Finset.card_union_of_disjoint hd, Nat.cast_add]
