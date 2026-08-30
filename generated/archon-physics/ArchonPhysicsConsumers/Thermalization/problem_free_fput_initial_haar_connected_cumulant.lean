import ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant

/-!
Consumer for finite partition/Möbius connected cumulants of initial iid Haar
FPUT histories.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

theorem supplied_joint_cumulant_partition_formula_consumer
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (blockMoment : Finset I → Complex) :
    suppliedJointCumulant blockMoment =
      ∑ partition : Finpartition (Finset.univ : Finset I),
        partitionMobiusCoefficient partition *
          ∏ block ∈ partition.parts, blockMoment block := rfl

theorem every_partition_has_unbalanced_block_consumer
    {Mode I : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    ∃ block ∈ partition.parts,
      indexedSignedTreeBlockCharge entry block ≠ 0 :=
  exists_unbalanced_block_of_totalCharge_ne_zero entry partition htotal

theorem every_unbalanced_partition_term_vanishes_consumer
    {Mode I : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    partitionMobiusCoefficient partition *
        (∏ block ∈ partition.parts,
          initialHaarSignedTreeBlockMoment entry block) = 0 :=
  initialHaar_partitionTerm_eq_zero_of_totalCharge_ne_zero
    entry partition htotal

/-- Charge-balanced blocks, including resonant triad/quartet configurations,
are retained by the initial Haar selector rather than declared zero. -/
theorem every_balanced_partition_term_is_retained_consumer
    {Mode I : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (hbalanced : ∀ block ∈ partition.parts,
      indexedSignedTreeBlockCharge entry block = 0) :
    partitionMobiusCoefficient partition *
        (∏ block ∈ partition.parts,
          initialHaarSignedTreeBlockMoment entry block) =
      partitionMobiusCoefficient partition :=
  initialHaar_partitionTerm_eq_mobius_of_all_blocks_balanced
    entry partition hbalanced

theorem initial_unbalanced_connected_cumulant_vanishes_consumer
    {Mode I : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (entry : I → SignedInteractionTree Mode)
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    initialHaarSignedTreeConnectedCumulant entry = 0 :=
  initialHaarSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    entry htotal

theorem actual_iid_unbalanced_connected_cumulant_vanishes_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (entry : I → SignedInteractionTree (Site N))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    actualIIDInitialSignedTreeConnectedCumulant ensemble entry = 0 :=
  actualIIDInitialSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    ensemble entry htotal

theorem actual_iid_fixed_root_raw_history_cumulant_vanishes_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (history : I → ArchonPhysics.FinitePhaseMonomials.PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)
    (htotal :
      fixedRootIndexedRawHistoryTotalCharge (I := I) (N := N) (r := r)
        rootMomentum history ≠ 0) :
    actualIIDFixedRootRawHistoryConnectedCumulant
      (I := I) (N := N) (r := r)
      ensemble rootMomentum history = 0 :=
  actualIIDFixedRootRawHistoryConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    (I := I) (N := N) (r := r)
    ensemble rootMomentum history htotal

#print axioms supplied_joint_cumulant_partition_formula_consumer
#print axioms every_partition_has_unbalanced_block_consumer
#print axioms every_unbalanced_partition_term_vanishes_consumer
#print axioms every_balanced_partition_term_is_retained_consumer
#print axioms initial_unbalanced_connected_cumulant_vanishes_consumer
#print axioms actual_iid_unbalanced_connected_cumulant_vanishes_consumer
#print axioms actual_iid_fixed_root_raw_history_cumulant_vanishes_consumer

end

end ArchonPhysicsConsumers.Thermalization
