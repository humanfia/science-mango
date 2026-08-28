import ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting

/-!
# Consumer endpoints for arbitrary-order free FPUT history counts

These endpoints expose the exact Catalan shape, sign, fixed-root momentum,
and tree-couple counts used by the high-order Picard layer.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting

noncomputable section

theorem freeFPUT_binaryShapes_catalan_consumer (r : Nat) :
    Fintype.card (BinaryInteractionTreeOfOrder r) = catalan r :=
  card_binaryInteractionTreeOfOrder r

theorem freeFPUT_branchSigns_fourPow_consumer {r : Nat}
    (tree : BinaryInteractionTreeOfOrder r) :
    Fintype.card (BinarySignDecoration tree.1) = 4 ^ r :=
  card_binarySignDecoration_of_order tree

theorem freeFPUT_fixedRootRawHistories_exact_consumer
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) =
      catalan r * 4 ^ r * N ^ r :=
  card_fixedRootRawHistoryIndex rootMomentum

theorem freeFPUT_fixedRootRawCouples_exact_consumer
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawCoupleIndex N r rootMomentum) =
      (catalan r * 4 ^ r * N ^ r) ^ 2 :=
  card_fixedRootRawCoupleIndex rootMomentum

theorem freeFPUT_fixedRootRawHistories_exponential_consumer
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) ≤
      16 ^ r * N ^ r :=
  card_fixedRootRawHistoryIndex_le rootMomentum

#print axioms freeFPUT_binaryShapes_catalan_consumer
#print axioms freeFPUT_branchSigns_fourPow_consumer
#print axioms freeFPUT_fixedRootRawHistories_exact_consumer
#print axioms freeFPUT_fixedRootRawCouples_exact_consumer
#print axioms freeFPUT_fixedRootRawHistories_exponential_consumer

end

end ArchonPhysicsConsumers.Thermalization
