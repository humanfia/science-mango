import ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration

/-!
Consumer audit for complete branching-history small-denominator enumeration.
-/

open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

example (gamma : Real) (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    FullyNonresonantBranchingHistory gamma tree assignment ↔
      ∀ delta ∈ branchingHistoryDenominators tree assignment,
        gamma ≤ |delta| :=
  fullyNonresonantBranchingHistory_iff_forall_mem_denominators
    gamma tree assignment

example (gamma : Real) (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    ¬ FullyNonresonantBranchingHistory gamma tree assignment ↔
      ∃ delta ∈ branchingHistoryDenominators tree assignment,
        |delta| < gamma :=
  not_fullyNonresonantBranchingHistory_iff_exists_small_denominator
    gamma tree assignment

example (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    (branchingHistoryDenominators tree assignment).length =
      (branchingPhaseLinearExtensions tree assignment).length *
        (2 ^ tree.order - 1) :=
  length_branchingHistoryDenominators tree assignment

#print axioms fullyNonresonantBranchingHistory_iff_forall_mem_denominators
#print axioms not_fullyNonresonantBranchingHistory_iff_exists_small_denominator
#print axioms length_flatMap_orderedHistoryDenominators_of_fixed_length
#print axioms length_branchingHistoryDenominators
