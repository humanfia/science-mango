import ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight

/-!
# Consumer endpoints for FPUT binary-history time-simplex weights
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight

noncomputable section

theorem freeFPUT_treeWeight_is_recursiveDuhamel_consumer
    (left right : BinaryInteractionTree) (T : Real) :
    (∫ t in (0 : Real)..T,
      binaryTreeTimeSimplexWeight left t *
        binaryTreeTimeSimplexWeight right t) =
      binaryTreeTimeSimplexWeight (.node left right) T :=
  integral_mul_binaryTreeTimeSimplexWeight left right T

theorem freeFPUT_fixedRoot_timeWeight_exactCountBound_consumer
    {N : Nat} [NeZero N] (r : Nat) (rootMomentum : Site N)
    {T : Real} (hT : 0 ≤ T) :
    fixedRootRawHistoryTimeWeight r rootMomentum T ≤
      (catalan r * 4 ^ r * N ^ r : Nat) * T ^ r :=
  fixedRootRawHistoryTimeWeight_le_exact_count r rootMomentum hT

theorem freeFPUT_fixedRoot_timeWeight_exponentialBound_consumer
    {N : Nat} [NeZero N] (r : Nat) (rootMomentum : Site N)
    {T : Real} (hT : 0 ≤ T) :
    fixedRootRawHistoryTimeWeight r rootMomentum T ≤
      (16 ^ r * N ^ r : Nat) * T ^ r :=
  fixedRootRawHistoryTimeWeight_le_exponential r rootMomentum hT

#print axioms freeFPUT_treeWeight_is_recursiveDuhamel_consumer
#print axioms freeFPUT_fixedRoot_timeWeight_exactCountBound_consumer
#print axioms freeFPUT_fixedRoot_timeWeight_exponentialBound_consumer

end

end ArchonPhysicsConsumers.Thermalization
