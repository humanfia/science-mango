import ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound

/-!
Named consumer for the order-only fully-nonresonant branching FPUT bound.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound

noncomputable section

/-- Linear-extension multiplicity is uniformly bounded over all phase
assignments and all binary shapes of a fixed interaction order. -/
theorem free_FPUT_branching_linear_extension_factorial_consumer
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    (branchingPhaseLinearExtensions tree assignment).length <=
      tree.order.factorial :=
  length_branchingPhaseLinearExtensions_le_factorial tree assignment

/-- A cumulative gap for every linear extension gives a deterministic
factorial-order bound for the genuine branching Duhamel integral. -/
theorem free_FPUT_fully_nonresonant_branching_order_bound_consumer
    {gamma : Real} (hgamma : 0 < gamma)
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    (hregular : FullyNonresonantBranchingHistory gamma tree assignment)
    (time : Real) :
    ‖branchingOscillatoryDuhamelIntegral tree assignment time‖ <=
      (tree.order.factorial : Real) * (2 / gamma) ^ tree.order :=
  norm_branchingOscillatoryDuhamelIntegral_le_factorial_order
    hgamma tree assignment hregular time

#print axioms free_FPUT_branching_linear_extension_factorial_consumer
#print axioms free_FPUT_fully_nonresonant_branching_order_bound_consumer

end

end ArchonPhysicsConsumers.Thermalization
