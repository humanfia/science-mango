import ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-!
# Catalan counting of arbitrary-order free FPUT interaction histories

The quadratic force in the alpha-FPUT chain generates rooted binary Picard
histories.  This file counts, at every perturbative order `r`, all of the raw
finite-volume choices which remain after fixing the output momentum:

* `catalan r` ordered binary interaction shapes;
* `4 ^ r` phase/conjugate choices on the two incoming edges at every vertex;
* `N ^ r` leaf-momentum assignments satisfying every vertex conservation law.

Thus the exact raw count is `catalan r * 4 ^ r * N ^ r`; a tree couple has the
square of this cardinality.  These are combinatorial inputs for a high-order
Picard/garden estimate.  No frequency denominator, analytic coefficient
bound, random-phase propagation, or kinetic equation is assumed here.
-/

namespace ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting

noncomputable section

/-! ## Identification with Mathlib's Catalan binary trees -/

/-- Forgetful identification with Mathlib's unit-labelled binary trees. -/
def fputTreeToCatalanTree : BinaryInteractionTree → BinaryTree Unit
  | .leaf => .nil
  | .node left right =>
      .node () (fputTreeToCatalanTree left) (fputTreeToCatalanTree right)

/-- Reconstruction from a unit-labelled Catalan binary tree. -/
def fputTreeOfCatalanTree : BinaryTree Unit → BinaryInteractionTree
  | .nil => .leaf
  | .node _ left right =>
      .node (fputTreeOfCatalanTree left) (fputTreeOfCatalanTree right)

@[simp] theorem fputTreeOf_toCatalan
    (tree : BinaryInteractionTree) :
    fputTreeOfCatalanTree (fputTreeToCatalanTree tree) = tree := by
  induction tree with
  | leaf => rfl
  | node left right hleft hright =>
      simp [fputTreeToCatalanTree, fputTreeOfCatalanTree,
        hleft, hright]

@[simp] theorem fputTreeTo_ofCatalan
    (tree : BinaryTree Unit) :
    fputTreeToCatalanTree (fputTreeOfCatalanTree tree) = tree := by
  induction tree with
  | nil => rfl
  | node value left right hleft hright =>
      cases value
      simp [fputTreeToCatalanTree, fputTreeOfCatalanTree,
        hleft, hright]

/-- Equivalence used to transport Mathlib's exact Catalan enumeration. -/
def catalanTreeEquiv : BinaryInteractionTree ≃ BinaryTree Unit where
  toFun := fputTreeToCatalanTree
  invFun := fputTreeOfCatalanTree
  left_inv := fputTreeOf_toCatalan
  right_inv := fputTreeTo_ofCatalan

@[simp] theorem numNodes_fputTreeToCatalanTree
    (tree : BinaryInteractionTree) :
    (fputTreeToCatalanTree tree).numNodes = tree.order := by
  induction tree with
  | leaf => rfl
  | node left right hleft hright =>
      simp [fputTreeToCatalanTree,
        BinaryInteractionTree.order, hleft, hright]

@[simp] theorem order_fputTreeOfCatalanTree
    (tree : BinaryTree Unit) :
    (fputTreeOfCatalanTree tree).order = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node value left right hleft hright =>
      cases value
      simp [fputTreeOfCatalanTree,
        BinaryInteractionTree.order, hleft, hright]

/-- Unsigned ordered binary interaction shapes with exactly `r` vertices. -/
abbrev BinaryInteractionTreeOfOrder (r : Nat) :=
  {tree : BinaryInteractionTree // tree.order = r}

/-- Exact-order shapes are the elements of Mathlib's Catalan finset. -/
def binaryInteractionTreeOfOrderEquivCatalanFinset (r : Nat) :
    BinaryInteractionTreeOfOrder r ≃
      {tree : BinaryTree Unit //
        tree ∈ BinaryTree.treesOfNumNodesEq r} where
  toFun tree :=
    ⟨fputTreeToCatalanTree tree.1,
      BinaryTree.mem_treesOfNumNodesEq.mpr (by
        simpa using tree.2)⟩
  invFun tree :=
    ⟨fputTreeOfCatalanTree tree.1,
      (order_fputTreeOfCatalanTree tree.1).trans
        (BinaryTree.mem_treesOfNumNodesEq.mp tree.2)⟩
  left_inv tree := by
    apply Subtype.ext
    exact fputTreeOf_toCatalan tree.1
  right_inv tree := by
    apply Subtype.ext
    exact fputTreeTo_ofCatalan tree.1

noncomputable instance binaryInteractionTreeOfOrderFintype (r : Nat) :
    Fintype (BinaryInteractionTreeOfOrder r) :=
  Fintype.ofEquiv
    {tree : BinaryTree Unit //
      tree ∈ BinaryTree.treesOfNumNodesEq r}
    (binaryInteractionTreeOfOrderEquivCatalanFinset r).symm

/-- There are exactly `catalan r` ordered quadratic interaction shapes of
order `r`. -/
theorem card_binaryInteractionTreeOfOrder (r : Nat) :
    Fintype.card (BinaryInteractionTreeOfOrder r) = catalan r := by
  calc
    Fintype.card (BinaryInteractionTreeOfOrder r) =
        Fintype.card
          {tree : BinaryTree Unit //
            tree ∈ BinaryTree.treesOfNumNodesEq r} :=
      Fintype.card_congr
        (binaryInteractionTreeOfOrderEquivCatalanFinset r)
    _ = (BinaryTree.treesOfNumNodesEq r).card :=
      Fintype.card_coe _
    _ = catalan r :=
      BinaryTree.treesOfNumNodesEq_card_eq_catalan r

/-! ## Branch-sign decorations -/

instance phaseSignFintype : Fintype PhaseSign where
  elems := {.phase, .conjugate}
  complete := by
    intro sign
    cases sign <;> simp

@[simp] theorem card_phaseSign : Fintype.card PhaseSign = 2 := by
  decide

/-- The two incoming phase/conjugate choices at every interaction vertex. -/
@[reducible]
def BinarySignDecoration : BinaryInteractionTree → Type
  | .leaf => PUnit
  | .node left right =>
      (PhaseSign × PhaseSign) ×
        (BinarySignDecoration left × BinarySignDecoration right)

@[instance_reducible]
noncomputable def binarySignDecorationFintype :
    (tree : BinaryInteractionTree) → Fintype (BinarySignDecoration tree)
  | .leaf => (inferInstance : Fintype PUnit)
  | .node left right =>
      @instFintypeProd (PhaseSign × PhaseSign)
        (BinarySignDecoration left × BinarySignDecoration right)
        (inferInstance : Fintype (PhaseSign × PhaseSign))
        (@instFintypeProd (BinarySignDecoration left)
          (BinarySignDecoration right)
          (binarySignDecorationFintype left)
          (binarySignDecorationFintype right))

@[instance_reducible]
noncomputable instance (tree : BinaryInteractionTree) :
    Fintype (BinarySignDecoration tree) :=
  binarySignDecorationFintype tree

/-- A fixed ordered shape of order `r` has exactly `4 ^ r` branch-sign
decorations. -/
theorem card_binarySignDecoration (tree : BinaryInteractionTree) :
    Fintype.card (BinarySignDecoration tree) = 4 ^ tree.order := by
  induction tree with
  | leaf =>
      simp [BinarySignDecoration, BinaryInteractionTree.order]
  | node left right hleft hright =>
      simp only [BinarySignDecoration, Fintype.card_prod,
        card_phaseSign, hleft, hright, BinaryInteractionTree.order]
      rw [pow_add, pow_succ]
      ring

/-- Turn a shape and all of its edge signs into the signed momentum tree used
by the exact fixed-root fibre theorem. -/
def signedMomentumTreeOfDecoration :
    (tree : BinaryInteractionTree) →
      BinarySignDecoration tree → SignedMomentumBinaryTree
  | .leaf, _ => .leaf
  | .node left right, decoration =>
      .node decoration.1.1 decoration.1.2
        (signedMomentumTreeOfDecoration left decoration.2.1)
        (signedMomentumTreeOfDecoration right decoration.2.2)

@[simp] theorem shape_signedMomentumTreeOfDecoration
    (tree : BinaryInteractionTree)
    (decoration : BinarySignDecoration tree) :
    (signedMomentumTreeOfDecoration tree decoration).shape = tree := by
  induction tree with
  | leaf => rfl
  | node left right hleft hright =>
      rcases decoration with ⟨⟨leftSign, rightSign⟩,
        leftDecoration, rightDecoration⟩
      simp [signedMomentumTreeOfDecoration,
        SignedMomentumBinaryTree.shape, hleft, hright]

theorem card_binarySignDecoration_of_order {r : Nat}
    (tree : BinaryInteractionTreeOfOrder r) :
    Fintype.card (BinarySignDecoration tree.1) = 4 ^ r := by
  rw [card_binarySignDecoration, tree.2]

/-! ## Exact raw history and couple counts at fixed output momentum -/

/-- One arbitrary-order raw FPUT history at fixed root: an ordered shape,
all incoming branch signs, and all leaf momenta satisfying the exact signed
root conservation law. -/
abbrev FixedRootRawHistoryIndex
    (N r : Nat) (rootMomentum : Site N) :=
  Σ tree : BinaryInteractionTreeOfOrder r,
    Σ decoration : BinarySignDecoration tree.1,
      {momentum :
          (signedMomentumTreeOfDecoration tree.1 decoration).LeafPosition →
            Site N //
        (signedMomentumTreeOfDecoration tree.1 decoration).leafMomentumToRoot
            momentum = rootMomentum}

noncomputable instance fixedRootRawHistoryIndexFintype
    (N r : Nat) [NeZero N] (rootMomentum : Site N) :
    Fintype (FixedRootRawHistoryIndex N r rootMomentum) :=
  inferInstance

theorem card_fixedRootLeafMomentumFiber
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (tree : BinaryInteractionTreeOfOrder r)
    (decoration : BinarySignDecoration tree.1) :
    Fintype.card
        {momentum :
            (signedMomentumTreeOfDecoration tree.1 decoration).LeafPosition →
              Site N //
          (signedMomentumTreeOfDecoration tree.1 decoration).leafMomentumToRoot
              momentum = rootMomentum} =
      N ^ r := by
  rw [SignedMomentumBinaryTree.card_leafMomentumToRootFiber_eq_pow_order]
  simp [tree.2]

/-- Exact arbitrary-order raw history count at fixed output momentum. -/
theorem card_fixedRootRawHistoryIndex
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) =
      catalan r * 4 ^ r * N ^ r := by
  classical
  change Fintype.card
      (Σ tree : BinaryInteractionTreeOfOrder r,
        Σ decoration : BinarySignDecoration tree.1,
          {momentum :
              (signedMomentumTreeOfDecoration tree.1 decoration).LeafPosition →
                Site N //
            (signedMomentumTreeOfDecoration tree.1 decoration).leafMomentumToRoot
                momentum = rootMomentum}) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  simp_rw [card_fixedRootLeafMomentumFiber rootMomentum]
  simp_rw [Finset.sum_const, Finset.card_univ,
    card_binarySignDecoration_of_order]
  rw [Finset.sum_const, Finset.card_univ,
    card_binaryInteractionTreeOfOrder]
  ring

/-- A raw tree couple is the ordered pair appearing in a quadratic energy
moment. -/
abbrev FixedRootRawCoupleIndex
    (N r : Nat) (rootMomentum : Site N) :=
  FixedRootRawHistoryIndex N r rootMomentum ×
    FixedRootRawHistoryIndex N r rootMomentum

noncomputable instance fixedRootRawCoupleIndexFintype
    (N r : Nat) [NeZero N] (rootMomentum : Site N) :
    Fintype (FixedRootRawCoupleIndex N r rootMomentum) :=
  inferInstance

/-- Exact raw tree-couple count before Haar cancellation or denominator
estimates. -/
theorem card_fixedRootRawCoupleIndex
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawCoupleIndex N r rootMomentum) =
      (catalan r * 4 ^ r * N ^ r) ^ 2 := by
  rw [Fintype.card_prod,
    card_fixedRootRawHistoryIndex rootMomentum]
  ring

/-! ## A convenient exponential majorant -/

theorem catalan_le_four_pow (r : Nat) : catalan r ≤ 4 ^ r := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow r)

/-- The exact raw history family grows at most like `16 ^ r * N ^ r`.
This isolates the purely combinatorial exponential from the analytic
smallness required in a convergent high-order expansion. -/
theorem card_fixedRootRawHistoryIndex_le
    {N r : Nat} [NeZero N] (rootMomentum : Site N) :
    Fintype.card (FixedRootRawHistoryIndex N r rootMomentum) ≤
      16 ^ r * N ^ r := by
  rw [card_fixedRootRawHistoryIndex]
  calc
    catalan r * 4 ^ r * N ^ r ≤ 4 ^ r * 4 ^ r * N ^ r := by
      gcongr
      exact catalan_le_four_pow r
    _ = 16 ^ r * N ^ r := by
      rw [← mul_pow]
      norm_num

end

end ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
