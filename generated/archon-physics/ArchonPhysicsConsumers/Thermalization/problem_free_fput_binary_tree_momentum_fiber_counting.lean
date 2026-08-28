import ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting
open ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting.SignedMomentumBinaryTree

noncomputable section

/-- A finite family of `L` signed leaf momenta has exactly `N^(L-1)`
assignments at fixed total momentum. -/
theorem signedLeafMomentum_fixedRoot_exactCard_consumer
    {N : Nat} [NeZero N]
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf] [Nonempty Leaf]
    (sign : Leaf → PhaseSign) (rootMomentum : Site N) :
    Fintype.card
        {momentum : Leaf → Site N //
          signedMomentumSum sign momentum = rootMomentum} =
      N ^ (Fintype.card Leaf - 1) :=
  card_signedMomentumFiber sign rootMomentum

/-- For a fixed signed binary tree root, the number of free leaf momenta is
the number of leaves minus one. -/
theorem binaryTreeLeafMomentum_fixedRoot_exactCard_consumer
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        {momentum : tree.LeafPosition → Site N //
          tree.leafMomentumToRoot momentum = rootMomentum} =
      N ^ (tree.leafCount - 1) :=
  card_leafMomentumToRootFiber tree rootMomentum

/-- Every valid internal momentum label is uniquely reconstructed from the
literal leaves. -/
theorem validBinaryTreeMomentumDecoration_unique_consumer
    {N : Nat} (tree : SignedMomentumBinaryTree)
    {first second : FullMomentumDecoration N tree}
    (hfirst : IsMomentumValid tree first)
    (hsecond : IsMomentumValid tree second)
    (hleaves : decorationLeaves tree first = decorationLeaves tree second) :
    first = second :=
  validDecorations_eq_of_leaves_eq tree hfirst hsecond hleaves

/-- Direct diagram-counting endpoint.  A binary tree with `r` interaction
vertices has exactly `N^r` full momentum decorations at fixed root after all
vertex momentum constraints are imposed. -/
theorem binaryTreeFullMomentumDecoration_fixedRoot_exactCard_consumer
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        (FixedRootValidMomentumDecoration N tree rootMomentum) =
      N ^ tree.shape.order :=
  card_fixedRootValidMomentumDecoration_eq_pow_order tree rootMomentum

/-- The corresponding upper-bound interface for estimates that only consume
a volume power. -/
theorem binaryTreeFullMomentumDecoration_fixedRoot_card_le_consumer
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        (FixedRootValidMomentumDecoration N tree rootMomentum) ≤
      N ^ tree.shape.order := by
  exact le_of_eq
    (binaryTreeFullMomentumDecoration_fixedRoot_exactCard_consumer
      tree rootMomentum)

#print axioms signedLeafMomentum_fixedRoot_exactCard_consumer
#print axioms binaryTreeLeafMomentum_fixedRoot_exactCard_consumer
#print axioms validBinaryTreeMomentumDecoration_unique_consumer
#print axioms binaryTreeFullMomentumDecoration_fixedRoot_exactCard_consumer
#print axioms binaryTreeFullMomentumDecoration_fixedRoot_card_le_consumer

end

end ArchonPhysicsConsumers.Thermalization
