import FrozenTarget_1c2a7819f4ed60c4
theorem M7.RecoveryInstance.strict_decrease : QuantumHarnessFrozenTarget := by
  intro N inst w E bases hE hB hpos
  classical
  have hf := (M7.RecoveryInstance.fresh_leaf N w E bases hE hB hpos).1
  have hgood := (M7.RecoveryInstance.insert_good N w E bases hE hB hpos).1
  have ho : M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.ActualOrbit.orbit (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) := by
    apply (M7.CanonicalClasses.orbit_membership N _ _).2
    exact (M7.CanonicalClasses.idempotent N _).symm
  have hlt : (M7.RecoveryInstance.remaining w E (M7.RecoveryInstance.insertedBases w E bases) []).card < (M7.RecoveryInstance.remaining w E bases []).card := by
    unfold M7.RecoveryInstance.remaining M7.RecoveryInstance.insertedBases
    rw [M7.OrbitResidual.insert_remaining]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hm : M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E []) bases \ M7.ActualOrbit.orbit (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) := by
      rw [heq]
      exact hf
    exact (Finset.mem_sdiff.mp hm).2 ho
  refine ⟨hlt, ?_⟩
  rw [(M7.RecoveryInstance.count_card N w E (M7.RecoveryInstance.insertedBases w E bases) hE hgood []).2.1,
    (M7.RecoveryInstance.count_card N w E bases hE hB []).2.1]
  exact hlt
