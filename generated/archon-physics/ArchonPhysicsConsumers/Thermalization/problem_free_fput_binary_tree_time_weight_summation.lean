import ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation

/-!
# Consumer endpoints for exact binary-tree time-weight summation
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight
open ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation

noncomputable section

theorem freeFPUT_successorShape_rootSplit_consumer (r : Nat) :
    Nonempty (BinaryInteractionTreeOfOrder (r + 1) ≃
      BinaryInteractionTreeSuccessorSplit r) :=
  ⟨binaryInteractionTreeSuccessorEquiv r⟩

theorem freeFPUT_allShapeTimeWeights_sum_to_pow_consumer
    (r : Nat) (T : Real) :
    totalBinaryInteractionTreeTimeWeight r T = T ^ r :=
  totalBinaryInteractionTreeTimeWeight_eq_pow r T

theorem freeFPUT_fixedRootRawTimeWeight_noCatalan_consumer
    {N : Nat} [NeZero N] (r : Nat) (rootMomentum : Site N)
    (T : Real) :
    fixedRootRawHistoryTimeWeight r rootMomentum T =
      (4 ^ r * N ^ r : Nat) * T ^ r :=
  fixedRootRawHistoryTimeWeight_eq r rootMomentum T

#print axioms freeFPUT_successorShape_rootSplit_consumer
#print axioms freeFPUT_allShapeTimeWeights_sum_to_pow_consumer
#print axioms freeFPUT_fixedRootRawTimeWeight_noCatalan_consumer

end

end ArchonPhysicsConsumers.Thermalization
