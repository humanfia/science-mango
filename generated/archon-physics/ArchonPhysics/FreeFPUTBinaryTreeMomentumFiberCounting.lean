import ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

/-!
# Exact momentum-fibre counting for signed binary FPUT trees

This module supplies the first genuine volume-counting input for a binary
FPUT tree expansion.  For any nonempty finite family of `ZMod N` leaf
momenta with fixed signs `+1` or `-1`, every prescribed signed root momentum
has exactly `N^(L-1)` preimages.  The proof solves one pivot leaf explicitly;
it uses no frequency or resonance estimate.

The second half packages the statement for signed binary shapes.  It also
defines full internal-mode decorations, proves that the vertex momentum
constraints determine every internal mode uniquely from the leaves, and
deduces the same fixed-root upper bound for valid full decorations.

All results are exact finite-volume combinatorics.  No near-resonance count,
large-volume uniformity, kinetic equation, or WKE limit is asserted.
-/

namespace ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-! ## A general signed-sum fibre over `ZMod N` -/

/-- Action of a phase/conjugate sign on a Fourier momentum. -/
def phaseSignMomentum {N : Nat} : PhaseSign → Site N → Site N
  | .phase, momentum => momentum
  | .conjugate, momentum => -momentum

@[simp] theorem phaseSignMomentum_phase {N : Nat} (momentum : Site N) :
    phaseSignMomentum .phase momentum = momentum := rfl

@[simp] theorem phaseSignMomentum_conjugate {N : Nat} (momentum : Site N) :
    phaseSignMomentum .conjugate momentum = -momentum := rfl

/-- Signed sum of a finite family of Fourier leaf momenta. -/
def signedMomentumSum
    {N : Nat} {Leaf : Type*} [Fintype Leaf]
    (sign : Leaf → PhaseSign) (momentum : Leaf → Site N) : Site N :=
  ∑ leaf, phaseSignMomentum (sign leaf) (momentum leaf)

/-- The leaf values away from one chosen pivot. -/
abbrev AwayFrom {Leaf : Type*} (pivot : Leaf) := {leaf : Leaf // leaf ≠ pivot}

def signedMomentumAwaySum
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf)
    (momentum : AwayFrom pivot → Site N) : Site N :=
  ∑ leaf : AwayFrom pivot,
    phaseSignMomentum (sign leaf.1) (momentum leaf)

/-- Unique pivot value which closes a prescribed signed momentum sum. -/
def solveSignedMomentumPivot {N : Nat}
    (pivotSign : PhaseSign) (target awaySum : Site N) : Site N :=
  match pivotSign with
  | .phase => target - awaySum
  | .conjugate => awaySum - target

theorem away_add_signed_solve_eq_target
    {N : Nat} (pivotSign : PhaseSign) (target awaySum : Site N) :
    awaySum + phaseSignMomentum pivotSign
        (solveSignedMomentumPivot pivotSign target awaySum) = target := by
  cases pivotSign <;>
    simp [solveSignedMomentumPivot]

theorem solveSignedMomentumPivot_unique
    {N : Nat} (pivotSign : PhaseSign) (target awaySum value : Site N)
    (hvalue : awaySum + phaseSignMomentum pivotSign value = target) :
    value = solveSignedMomentumPivot pivotSign target awaySum := by
  cases pivotSign
  · simp only [solveSignedMomentumPivot, phaseSignMomentum_phase] at hvalue ⊢
    linear_combination hvalue
  · simp only [solveSignedMomentumPivot, phaseSignMomentum_conjugate] at hvalue ⊢
    linear_combination -hvalue

/-- Extend an assignment away from the pivot by the unique closing value. -/
def extendSignedMomentumAtPivot
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (target : Site N)
    (away : AwayFrom pivot → Site N) : Leaf → Site N :=
  fun leaf ↦ if h : leaf = pivot then
    solveSignedMomentumPivot (sign pivot) target
      (signedMomentumAwaySum sign pivot away)
  else away ⟨leaf, h⟩

@[simp] theorem extendSignedMomentumAtPivot_pivot
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (target : Site N)
    (away : AwayFrom pivot → Site N) :
    extendSignedMomentumAtPivot sign pivot target away pivot =
      solveSignedMomentumPivot (sign pivot) target
        (signedMomentumAwaySum sign pivot away) := by
  simp [extendSignedMomentumAtPivot]

@[simp] theorem extendSignedMomentumAtPivot_away
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (target : Site N)
    (away : AwayFrom pivot → Site N) (leaf : AwayFrom pivot) :
    extendSignedMomentumAtPivot sign pivot target away leaf.1 = away leaf := by
  simp [extendSignedMomentumAtPivot, leaf.2]

theorem signedMomentumSum_eq_away_add_pivot
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (momentum : Leaf → Site N) :
    signedMomentumSum sign momentum =
      signedMomentumAwaySum sign pivot (fun leaf ↦ momentum leaf.1) +
        phaseSignMomentum (sign pivot) (momentum pivot) := by
  unfold signedMomentumSum signedMomentumAwaySum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ pivot]
  exact add_comm _ _

theorem signedMomentumSum_extendSignedMomentumAtPivot
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (target : Site N)
    (away : AwayFrom pivot → Site N) :
    signedMomentumSum sign
        (extendSignedMomentumAtPivot sign pivot target away) = target := by
  rw [signedMomentumSum_eq_away_add_pivot sign pivot]
  have haway :
      signedMomentumAwaySum sign pivot
          (fun leaf ↦
            extendSignedMomentumAtPivot sign pivot target away leaf.1) =
        signedMomentumAwaySum sign pivot away := by
    unfold signedMomentumAwaySum
    apply Finset.sum_congr rfl
    intro leaf _hleaf
    apply congrArg (phaseSignMomentum (sign leaf.1))
    exact extendSignedMomentumAtPivot_away sign pivot target away leaf
  rw [haway, extendSignedMomentumAtPivot_pivot]
  exact away_add_signed_solve_eq_target _ _ _

/-- Explicit equivalence: freely choose every leaf except the pivot, then
solve the remaining `±1` coefficient. -/
def awayAssignmentsEquivSignedMomentumFiber
    {N : Nat} {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sign : Leaf → PhaseSign) (pivot : Leaf) (target : Site N) :
    (AwayFrom pivot → Site N) ≃
      {momentum : Leaf → Site N // signedMomentumSum sign momentum = target} where
  toFun away :=
    ⟨extendSignedMomentumAtPivot sign pivot target away,
      signedMomentumSum_extendSignedMomentumAtPivot sign pivot target away⟩
  invFun momentum := fun leaf ↦ momentum.1 leaf.1
  left_inv away := by
    funext leaf
    exact extendSignedMomentumAtPivot_away sign pivot target away leaf
  right_inv momentum := by
    apply Subtype.ext
    funext leaf
    by_cases hleaf : leaf = pivot
    · subst leaf
      change extendSignedMomentumAtPivot sign pivot target
          (fun other ↦ momentum.1 other.1) pivot = momentum.1 pivot
      rw [extendSignedMomentumAtPivot_pivot]
      symm
      apply solveSignedMomentumPivot_unique
        (sign pivot) target
        (signedMomentumAwaySum sign pivot
          (fun other ↦ momentum.1 other.1))
        (momentum.1 pivot)
      rw [← signedMomentumSum_eq_away_add_pivot sign pivot momentum.1]
      exact momentum.2
    · exact extendSignedMomentumAtPivot_away sign pivot target
        (fun other ↦ momentum.1 other.1) ⟨leaf, hleaf⟩

theorem card_awayFrom
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf] (pivot : Leaf) :
    Fintype.card (AwayFrom pivot) = Fintype.card Leaf - 1 := by
  rw [show Fintype.card (AwayFrom pivot) =
      Fintype.card {leaf : Leaf // ¬ leaf = pivot} by rfl]
  rw [Fintype.card_subtype_compl (fun leaf : Leaf ↦ leaf = pivot)]
  simp

/-- Exact fixed-root fibre cardinality for every nonempty finite signed leaf
family. -/
theorem card_signedMomentumFiber
    {N : Nat} [NeZero N]
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf] [Nonempty Leaf]
    (sign : Leaf → PhaseSign) (target : Site N) :
    Fintype.card
        {momentum : Leaf → Site N // signedMomentumSum sign momentum = target} =
      N ^ (Fintype.card Leaf - 1) := by
  let pivot : Leaf := Classical.choice (inferInstance : Nonempty Leaf)
  calc
    Fintype.card
        {momentum : Leaf → Site N // signedMomentumSum sign momentum = target} =
        Fintype.card (AwayFrom pivot → Site N) :=
      (Fintype.card_congr
        (awayAssignmentsEquivSignedMomentumFiber sign pivot target)).symm
    _ = Fintype.card (Site N) ^ Fintype.card (AwayFrom pivot) := by
      rw [Fintype.card_fun]
    _ = N ^ (Fintype.card Leaf - 1) := by
      rw [ZMod.card, card_awayFrom]

/-! ## Signed binary shapes and their leaf-to-root momentum map -/

/-- A binary interaction shape together with the phase/conjugate branch
chosen on every edge out of an interaction vertex.  Its unsigned shape is
the one used by `PhyslibFPUTBinaryInteractionTreeCouples`. -/
inductive SignedMomentumBinaryTree where
  | leaf
  | node (leftSign rightSign : PhaseSign)
      (left right : SignedMomentumBinaryTree)
  deriving DecidableEq, Repr

namespace SignedMomentumBinaryTree

/-- Forget the branch signs, retaining the shared binary interaction shape. -/
def shape : SignedMomentumBinaryTree → BinaryInteractionTree
  | .leaf => .leaf
  | .node _ _ left right => .node left.shape right.shape

/-- Literal leaf occurrences; a repeated Fourier mode still occupies a
separate position in this type. -/
@[reducible]
def LeafPosition : SignedMomentumBinaryTree → Type
  | .leaf => PUnit
  | .node _ _ left right => left.LeafPosition ⊕ right.LeafPosition

@[instance_reducible]
noncomputable def leafPositionFintype :
    (tree : SignedMomentumBinaryTree) → Fintype tree.LeafPosition
  | .leaf => (inferInstance : Fintype PUnit)
  | .node _ _ left right =>
      @instFintypeSum left.LeafPosition right.LeafPosition
        (leafPositionFintype left) (leafPositionFintype right)

@[instance_reducible]
noncomputable instance (tree : SignedMomentumBinaryTree) :
    Fintype tree.LeafPosition :=
  leafPositionFintype tree

noncomputable instance (tree : SignedMomentumBinaryTree) :
    DecidableEq tree.LeafPosition :=
  Classical.decEq _

instance leafPositionNonempty (tree : SignedMomentumBinaryTree) :
    Nonempty tree.LeafPosition := by
  induction tree with
  | leaf => exact ⟨PUnit.unit⟩
  | node leftSign rightSign left right hleft hright =>
      exact ⟨Sum.inl (Classical.choice hleft)⟩

/-- Number of literal leaves, expressed through the shared tree shape. -/
def leafCount (tree : SignedMomentumBinaryTree) : Nat :=
  tree.shape.leafCount

theorem card_leafPosition (tree : SignedMomentumBinaryTree) :
    Fintype.card tree.LeafPosition = tree.leafCount := by
  induction tree with
  | leaf =>
      calc
        Fintype.card leaf.LeafPosition = Fintype.card PUnit :=
          Fintype.card_congr (Equiv.refl PUnit)
        _ = 1 := Fintype.card_unique
  | node leftSign rightSign left right hleft hright =>
      calc
        Fintype.card (node leftSign rightSign left right).LeafPosition =
            Fintype.card (left.LeafPosition ⊕ right.LeafPosition) :=
          Fintype.card_congr (Equiv.refl _)
        _ = Fintype.card left.LeafPosition +
            Fintype.card right.LeafPosition := Fintype.card_sum
        _ = (node leftSign rightSign left right).leafCount := by
          rw [hleft, hright]
          rfl

/-- Net sign transported from a leaf occurrence to the root. -/
def leafPathSign :
    (tree : SignedMomentumBinaryTree) → tree.LeafPosition → PhaseSign
  | .leaf, _ => .phase
  | .node leftSign _ left _, Sum.inl position =>
      composePhaseSign leftSign (left.leafPathSign position)
  | .node _ rightSign _ right, Sum.inr position =>
      composePhaseSign rightSign (right.leafPathSign position)

/-- Root momentum determined by all leaf momenta and all branch signs. -/
def leafMomentumToRoot {N : Nat} (tree : SignedMomentumBinaryTree)
    (momentum : tree.LeafPosition → Site N) : Site N :=
  signedMomentumSum tree.leafPathSign momentum

/-- Deng-style volume count: at fixed root momentum, exactly one leaf is
constrained and all other leaves are free.  The exponent is the number of
literal leaves minus one; no frequency shell is imposed here. -/
theorem card_leafMomentumToRootFiber
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        {momentum : tree.LeafPosition → Site N //
          tree.leafMomentumToRoot momentum = rootMomentum} =
      N ^ (tree.leafCount - 1) := by
  rw [← card_leafPosition tree]
  exact card_signedMomentumFiber tree.leafPathSign rootMomentum

theorem leafCount_eq_shape_order_add_one (tree : SignedMomentumBinaryTree) :
    tree.leafCount = tree.shape.order + 1 :=
  BinaryInteractionTree.leafCount_eq_order_add_one tree.shape

/-- Equivalent perturbative-order form of the fixed-root volume count: a
binary tree of order `r` has exactly `r` free leaf momenta after fixing its
root. -/
theorem card_leafMomentumToRootFiber_eq_pow_order
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        {momentum : tree.LeafPosition → Site N //
          tree.leafMomentumToRoot momentum = rootMomentum} =
      N ^ tree.shape.order := by
  rw [card_leafMomentumToRootFiber,
    leafCount_eq_shape_order_add_one]
  simp

theorem phaseSignMomentum_compose
    {N : Nat} (outer inner : PhaseSign) (momentum : Site N) :
    phaseSignMomentum (composePhaseSign outer inner) momentum =
      phaseSignMomentum outer (phaseSignMomentum inner momentum) := by
  cases outer <;> cases inner <;>
    simp [composePhaseSign]

theorem signedMomentumSum_composePhaseSign
    {N : Nat} {Leaf : Type*} [Fintype Leaf]
    (outer : PhaseSign) (sign : Leaf → PhaseSign)
    (momentum : Leaf → Site N) :
    signedMomentumSum (fun leaf ↦ composePhaseSign outer (sign leaf)) momentum =
      phaseSignMomentum outer (signedMomentumSum sign momentum) := by
  cases outer
  · simp [signedMomentumSum, composePhaseSign]
  · simp only [signedMomentumSum, phaseSignMomentum_compose]
    simp [phaseSignMomentum]

theorem signedMomentumSum_sum_type
    {N : Nat} {Left Right : Type*} [Fintype Left] [Fintype Right]
    (sign : Left ⊕ Right → PhaseSign) (momentum : Left ⊕ Right → Site N) :
    signedMomentumSum sign momentum =
      signedMomentumSum (fun position ↦ sign (Sum.inl position))
          (fun position ↦ momentum (Sum.inl position)) +
        signedMomentumSum (fun position ↦ sign (Sum.inr position))
          (fun position ↦ momentum (Sum.inr position)) := by
  unfold signedMomentumSum
  rw [Fintype.sum_sum_type]

theorem leafMomentumToRoot_node
    {N : Nat} (leftSign rightSign : PhaseSign)
    (left right : SignedMomentumBinaryTree)
    (momentum :
      (SignedMomentumBinaryTree.node leftSign rightSign left right).LeafPosition →
        Site N) :
    SignedMomentumBinaryTree.leafMomentumToRoot
        (SignedMomentumBinaryTree.node leftSign rightSign left right) momentum =
      phaseSignMomentum leftSign
          (left.leafMomentumToRoot (fun position ↦ momentum (Sum.inl position))) +
        phaseSignMomentum rightSign
          (right.leafMomentumToRoot
            (fun position ↦ momentum (Sum.inr position))) := by
  unfold leafMomentumToRoot
  rw [signedMomentumSum_sum_type]
  change
    signedMomentumSum
        (fun position ↦ composePhaseSign leftSign (left.leafPathSign position))
        (fun position ↦ momentum (Sum.inl position)) +
      signedMomentumSum
        (fun position ↦ composePhaseSign rightSign (right.leafPathSign position))
        (fun position ↦ momentum (Sum.inr position)) = _
  rw [signedMomentumSum_composePhaseSign,
    signedMomentumSum_composePhaseSign]

/-! ## Full internal momentum decorations -/

/-- Momentum labels on every edge of a fixed signed tree.  At a vertex the
first component is the output/root edge and the remaining components are the
two recursively decorated children. -/
@[reducible]
def FullMomentumDecoration (N : Nat) : SignedMomentumBinaryTree → Type
  | .leaf => Site N
  | .node _ _ left right =>
      Site N × (FullMomentumDecoration N left × FullMomentumDecoration N right)

@[instance_reducible]
noncomputable def fullMomentumDecorationFintype (N : Nat) [NeZero N] :
    (tree : SignedMomentumBinaryTree) → Fintype (FullMomentumDecoration N tree)
  | .leaf => (inferInstance : Fintype (Site N))
  | .node _ _ left right =>
      @instFintypeProd (Site N)
        (FullMomentumDecoration N left × FullMomentumDecoration N right)
        (inferInstance : Fintype (Site N))
        (@instFintypeProd (FullMomentumDecoration N left)
          (FullMomentumDecoration N right)
          (fullMomentumDecorationFintype N left)
          (fullMomentumDecorationFintype N right))

@[instance_reducible]
noncomputable instance (N : Nat) [NeZero N]
    (tree : SignedMomentumBinaryTree) :
    Fintype (FullMomentumDecoration N tree) :=
  fullMomentumDecorationFintype N tree

/-- Output momentum recorded at the root edge. -/
def decorationRoot {N : Nat} :
    (tree : SignedMomentumBinaryTree) → FullMomentumDecoration N tree → Site N
  | .leaf, momentum => momentum
  | .node _ _ _ _, decoration => decoration.1

/-- Restriction of a full decoration to its literal leaves. -/
def decorationLeaves {N : Nat} :
    (tree : SignedMomentumBinaryTree) →
      FullMomentumDecoration N tree → tree.LeafPosition → Site N
  | .leaf, momentum, _ => momentum
  | .node _ _ left _, decoration, Sum.inl position =>
      decorationLeaves left decoration.2.1 position
  | .node _ _ _ right, decoration, Sum.inr position =>
      decorationLeaves right decoration.2.2 position

/-- Every internal output obeys its signed vertex momentum constraint. -/
def IsMomentumValid {N : Nat} :
    (tree : SignedMomentumBinaryTree) → FullMomentumDecoration N tree → Prop
  | .leaf, _ => True
  | .node leftSign rightSign left right, decoration =>
      IsMomentumValid left decoration.2.1 ∧
        IsMomentumValid right decoration.2.2 ∧
        decoration.1 =
          phaseSignMomentum leftSign (decorationRoot left decoration.2.1) +
            phaseSignMomentum rightSign (decorationRoot right decoration.2.2)

/-- Canonical completion: choose the leaves freely and recursively compute
every internal output using the vertex momentum law. -/
def completeMomentumDecoration {N : Nat} :
    (tree : SignedMomentumBinaryTree) →
      (tree.LeafPosition → Site N) → FullMomentumDecoration N tree
  | .leaf, momentum => momentum PUnit.unit
  | .node leftSign rightSign left right, momentum =>
      let leftDecoration :=
        completeMomentumDecoration left (fun position ↦ momentum (Sum.inl position))
      let rightDecoration :=
        completeMomentumDecoration right (fun position ↦ momentum (Sum.inr position))
      (phaseSignMomentum leftSign (decorationRoot left leftDecoration) +
          phaseSignMomentum rightSign (decorationRoot right rightDecoration),
        (leftDecoration, rightDecoration))

theorem decorationLeaves_complete
    {N : Nat} (tree : SignedMomentumBinaryTree)
    (momentum : tree.LeafPosition → Site N) :
    decorationLeaves tree (completeMomentumDecoration tree momentum) = momentum := by
  induction tree with
  | leaf =>
      funext position
      cases position
      rfl
  | node leftSign rightSign left right hleft hright =>
      funext position
      cases position with
      | inl position =>
          exact congrFun
            (hleft (fun childPosition ↦ momentum (Sum.inl childPosition))) position
      | inr position =>
          exact congrFun
            (hright (fun childPosition ↦ momentum (Sum.inr childPosition))) position

theorem completeMomentumDecoration_valid
    {N : Nat} (tree : SignedMomentumBinaryTree)
    (momentum : tree.LeafPosition → Site N) :
    IsMomentumValid tree (completeMomentumDecoration tree momentum) := by
  induction tree with
  | leaf => trivial
  | node leftSign rightSign left right hleft hright =>
      exact ⟨hleft _, hright _, rfl⟩

theorem decorationRoot_complete
    {N : Nat} (tree : SignedMomentumBinaryTree)
    (momentum : tree.LeafPosition → Site N) :
    decorationRoot tree (completeMomentumDecoration tree momentum) =
      tree.leafMomentumToRoot momentum := by
  induction tree with
  | leaf =>
      simp [completeMomentumDecoration, decorationRoot,
        leafMomentumToRoot, signedMomentumSum, leafPathSign]
  | node leftSign rightSign left right hleft hright =>
      rw [leafMomentumToRoot_node]
      change
        phaseSignMomentum leftSign
            (decorationRoot left
              (completeMomentumDecoration left
                (fun position ↦ momentum (Sum.inl position)))) +
          phaseSignMomentum rightSign
            (decorationRoot right
              (completeMomentumDecoration right
                (fun position ↦ momentum (Sum.inr position)))) = _
      rw [hleft, hright]

/-- The vertex constraints leave no freedom in an internal label: the full
decoration is the canonical recursive completion of its own leaves. -/
theorem complete_decorationLeaves_eq_of_valid
    {N : Nat} (tree : SignedMomentumBinaryTree)
    (decoration : FullMomentumDecoration N tree)
    (hvalid : IsMomentumValid tree decoration) :
    completeMomentumDecoration tree (decorationLeaves tree decoration) =
      decoration := by
  induction tree with
  | leaf => rfl
  | node leftSign rightSign left right hleft hright =>
      rcases decoration with ⟨rootMomentum, leftDecoration, rightDecoration⟩
      rcases hvalid with ⟨hleftValid, hrightValid, hroot⟩
      change rootMomentum =
        phaseSignMomentum leftSign (decorationRoot left leftDecoration) +
          phaseSignMomentum rightSign (decorationRoot right rightDecoration)
        at hroot
      simp only [decorationLeaves, completeMomentumDecoration]
      rw [hleft leftDecoration hleftValid, hright rightDecoration hrightValid]
      change
        (phaseSignMomentum leftSign (decorationRoot left leftDecoration) +
            phaseSignMomentum rightSign (decorationRoot right rightDecoration),
          (leftDecoration, rightDecoration)) =
        (rootMomentum, (leftDecoration, rightDecoration))
      exact congrArg (fun root ↦ (root, (leftDecoration, rightDecoration))) hroot.symm

theorem validDecorations_eq_of_leaves_eq
    {N : Nat} (tree : SignedMomentumBinaryTree)
    {first second : FullMomentumDecoration N tree}
    (hfirst : IsMomentumValid tree first)
    (hsecond : IsMomentumValid tree second)
    (hleaves : decorationLeaves tree first = decorationLeaves tree second) :
    first = second := by
  rw [← complete_decorationLeaves_eq_of_valid tree first hfirst,
    ← complete_decorationLeaves_eq_of_valid tree second hsecond,
    hleaves]

/-- On a valid full decoration, the recursively recorded root equals the
literal signed sum of the free leaves. -/
theorem decorationRoot_eq_leafMomentumToRoot_of_valid
    {N : Nat} (tree : SignedMomentumBinaryTree)
    (decoration : FullMomentumDecoration N tree)
    (hvalid : IsMomentumValid tree decoration) :
    decorationRoot tree decoration =
      tree.leafMomentumToRoot (decorationLeaves tree decoration) := by
  calc
    decorationRoot tree decoration =
        decorationRoot tree
          (completeMomentumDecoration tree (decorationLeaves tree decoration)) :=
      congrArg (decorationRoot tree)
        (complete_decorationLeaves_eq_of_valid tree decoration hvalid).symm
    _ = tree.leafMomentumToRoot (decorationLeaves tree decoration) :=
      decorationRoot_complete tree _

/-- Full internal decorations obeying every vertex law and carrying one
prescribed root momentum. -/
abbrev FixedRootValidMomentumDecoration
    (N : Nat) (tree : SignedMomentumBinaryTree) (rootMomentum : Site N) :=
  {decoration : FullMomentumDecoration N tree //
    IsMomentumValid tree decoration ∧
      decorationRoot tree decoration = rootMomentum}

@[instance_reducible]
noncomputable instance fixedRootValidMomentumDecorationFintype
    (N : Nat) [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype (FixedRootValidMomentumDecoration N tree rootMomentum) :=
  Fintype.ofFinite _

/-- Valid internal decorations at fixed root are exactly the fixed-root leaf
fibre.  This records both uniqueness and existence of every internal mode
assignment; no frequency condition enters the equivalence. -/
def fixedRootValidDecorationsEquivLeafFiber
    {N : Nat} (tree : SignedMomentumBinaryTree) (rootMomentum : Site N) :
    FixedRootValidMomentumDecoration N tree rootMomentum ≃
      {momentum : tree.LeafPosition → Site N //
        tree.leafMomentumToRoot momentum = rootMomentum} where
  toFun decoration :=
    ⟨decorationLeaves tree decoration.1, by
      rw [← decorationRoot_eq_leafMomentumToRoot_of_valid
        tree decoration.1 decoration.2.1]
      exact decoration.2.2⟩
  invFun momentum :=
    ⟨completeMomentumDecoration tree momentum.1,
      completeMomentumDecoration_valid tree momentum.1,
      (decorationRoot_complete tree momentum.1).trans momentum.2⟩
  left_inv decoration := by
    apply Subtype.ext
    exact complete_decorationLeaves_eq_of_valid
      tree decoration.1 decoration.2.1
  right_inv momentum := by
    apply Subtype.ext
    exact decorationLeaves_complete tree momentum.1

/-- Exact number of valid full momentum decorations at fixed root.  All
internal labels cost no additional volume power beyond the free leaves. -/
theorem card_fixedRootValidMomentumDecoration
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        (FixedRootValidMomentumDecoration N tree rootMomentum) =
      N ^ (tree.leafCount - 1) := by
  classical
  calc
    Fintype.card (FixedRootValidMomentumDecoration N tree rootMomentum) =
        Fintype.card
          {momentum : tree.LeafPosition → Site N //
            tree.leafMomentumToRoot momentum = rootMomentum} :=
      Fintype.card_congr
        (fixedRootValidDecorationsEquivLeafFiber tree rootMomentum)
    _ = N ^ (tree.leafCount - 1) :=
      card_leafMomentumToRootFiber tree rootMomentum

/-- Terminal form for diagram counting: for a binary interaction tree of
order `r`, a fixed root admits exactly `N^r` momentum decorations satisfying
all vertex conservation laws. -/
theorem card_fixedRootValidMomentumDecoration_eq_pow_order
    {N : Nat} [NeZero N] (tree : SignedMomentumBinaryTree)
    (rootMomentum : Site N) :
    Fintype.card
        (FixedRootValidMomentumDecoration N tree rootMomentum) =
      N ^ tree.shape.order := by
  rw [card_fixedRootValidMomentumDecoration,
    leafCount_eq_shape_order_add_one]
  simp

end SignedMomentumBinaryTree

end

end ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting
